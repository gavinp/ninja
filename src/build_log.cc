// Copyright 2011 Google Inc. All Rights Reserved.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#include "build_log.h"

#include <errno.h>
#include <iostream>
#include <stdlib.h>
#include <string.h>
#include <sstream>

#ifndef _WIN32
#define __STDC_FORMAT_MACROS
#include <inttypes.h>
#include <unistd.h>
#endif

#include "build.h"
#include "graph.h"
#include "metrics.h"
#include "util.h"

// Implementation details:
// Each run's log appends to the most recent log file.
// To load, we run through all log entries in series, throwing away
// older runs.
// Once the number of redundant entries exceeds a threshold, we write
// out a new file and replace the existing one with it.

namespace {

const char kFileSignature[] = "# ninja log v%d\n";
const int kOldestSupportedVersion = 4;
const int kCurrentVersion = 5;

// 64bit MurmurHash2, by Austin Appleby
#if defined(_MSC_VER)
#define BIG_CONSTANT(x) (x)
#else   // defined(_MSC_VER)
#define BIG_CONSTANT(x) (x##LLU)
#endif // !defined(_MSC_VER)
inline
uint64_t MurmurHash64A(const void* key, int len) {
  static const uint64_t seed = 0xDECAFBADDECAFBADull;
  const uint64_t m = BIG_CONSTANT(0xc6a4a7935bd1e995);
  const int r = 47;
  uint64_t h = seed ^ (len * m);
  const uint64_t * data = (const uint64_t *)key;
  const uint64_t * end = data + (len/8);
  while(data != end) {
    uint64_t k = *data++;
    k *= m; 
    k ^= k >> r; 
    k *= m; 
    h ^= k;
    h *= m; 
  }
  const unsigned char* data2 = (const unsigned char*)data;
  switch(len & 7)
  {
  case 7: h ^= uint64_t(data2[6]) << 48;
  case 6: h ^= uint64_t(data2[5]) << 40;
  case 5: h ^= uint64_t(data2[4]) << 32;
  case 4: h ^= uint64_t(data2[3]) << 24;
  case 3: h ^= uint64_t(data2[2]) << 16;
  case 2: h ^= uint64_t(data2[1]) << 8;
  case 1: h ^= uint64_t(data2[0]);
          h *= m;
  };
  h ^= h >> r;
  h *= m;
  h ^= h >> r;
  return h;
} 
#undef BIG_CONSTANT


string ActualLogPath(const string& path, int number) {
  ostringstream actual_path_stream;
  actual_path_stream << path << "." << number;
  return number == 0 ? path : actual_path_stream.str();
}

}  // namespace

// static
uint64_t BuildLog::LogEntry::HashCommand(StringPiece command) {
  return MurmurHash64A(command.str_, command.len_);
}

BuildLog::BuildLog()
    : log_file_(NULL), config_(NULL), needs_rotation_(false), 
      needs_recompaction_(false) {}

BuildLog::~BuildLog() {
  Close();
}

bool BuildLog::OpenForWrite(const string& path, string* err) {
  if (config_ && config_->dry_run)
    return true;  // Do nothing, report success.

  if (needs_recompaction_) {
    Close();
    if (!Recompact(path, err))
      return false;
    max_log_file_number_ = 0;
    if (!Rotate(path, err))
      return false;
  }
  else {
    if (!pending_log_drops_.empty()) {
      if (!DropLogs(path, err))
        return false;
    }
    if (needs_rotation_) {
      Close();
      if (!Rotate(path, err))
        return false;
    }
  }

  log_file_ = fopen(path.c_str(), "ab");
  if (!log_file_) {
    *err = strerror(errno);
    return false;
  }
  setvbuf(log_file_, NULL, _IOLBF, BUFSIZ);
  SetCloseOnExec(fileno(log_file_));

  // Opening a file in append mode doesn't set the file pointer to the file's
  // end on Windows. Do that explicitly.
  fseek(log_file_, 0, SEEK_END);

  if (ftell(log_file_) == 0) {
    if (fprintf(log_file_, kFileSignature, kCurrentVersion) < 0) {
      *err = strerror(errno);
      return false;
    }
  }

  return true;
}

void BuildLog::RecordCommand(Edge* edge, int start_time, int end_time,
                             TimeStamp restat_mtime) {
  string command = edge->EvaluateCommand(true);
  for (vector<Node*>::iterator out = edge->outputs_.begin();
       out != edge->outputs_.end(); ++out) {
    const string& path = (*out)->path();
    Log::iterator i = log_.find(path);
    LogEntry* log_entry;
    if (i != log_.end()) {
      log_entry = i->second;
    } else {
      log_entry = new LogEntry;
      log_entry->output = path;
      log_.insert(Log::value_type(log_entry->output, log_entry));
    }
    log_entry->command_hash = LogEntry::HashCommand(command);
    log_entry->start_time = start_time;
    log_entry->end_time = end_time;
    log_entry->restat_mtime = restat_mtime;

    if (log_file_)
      WriteEntry(log_file_, *log_entry);
  }
}

void BuildLog::Close() {
  if (log_file_)
    fclose(log_file_);
  log_file_ = NULL;
}

class LineReader {
 public:
  explicit LineReader(FILE* file)
    : file_(file), buf_end_(buf_), line_start_(buf_), line_end_(NULL) {}

  // Reads a \n-terminated line from the file passed to the constructor.
  // On return, *line_start points to the beginning of the next line, and
  // *line_end points to the \n at the end of the line. If no newline is seen
  // in a fixed buffer size, *line_end is set to NULL. Returns false on EOF.
  bool ReadLine(char** line_start, char** line_end) {
    if (line_start_ >= buf_end_ || !line_end_) {
      // Buffer empty, refill.
      size_t size_read = fread(buf_, 1, sizeof(buf_), file_);
      if (!size_read)
        return false;
      line_start_ = buf_;
      buf_end_ = buf_ + size_read;
    } else {
      // Advance to next line in buffer.
      line_start_ = line_end_ + 1;
    }

    line_end_ = (char*)memchr(line_start_, '\n', buf_end_ - line_start_);
    if (!line_end_) {

      // No newline. Move rest of data to start of buffer, fill rest.
      size_t already_consumed = line_start_ - buf_;
      size_t size_rest = (buf_end_ - buf_) - already_consumed;
      memmove(buf_, line_start_, size_rest);

      size_t read = fread(buf_ + size_rest, 1, sizeof(buf_) - size_rest, file_);
      buf_end_ = buf_ + size_rest + read;
      line_start_ = buf_;
      line_end_ = (char*)memchr(line_start_, '\n', buf_end_ - line_start_);
    }

    *line_start = line_start_;
    *line_end = line_end_;
    return true;
  }

 private:
  FILE* file_;
  char buf_[256 << 10];
  char* buf_end_;  // Points one past the last valid byte in |buf_|.

  char* line_start_;
  // Points at the next \n in buf_ after line_start, or NULL.
  char* line_end_;
};

bool BuildLog::Load(const string& path, string* err) {
  METRIC_RECORD(".ninja_log load");
  
  int log_version = 0;
  unsigned first_file_entry_count = 0;
  unsigned total_entry_count = 0;
  
  for (int log_file_number=0;;++log_file_number) {
    string actual_path = ActualLogPath(path, log_file_number);

    FILE* file = fopen(actual_path.c_str(), "r");
    if (!file) {
      if (errno == ENOENT)
        break;
      *err = strerror(errno);
      return false;
    }
    max_log_file_number_ = log_file_number;

    LineReader reader(file);
    char* line_start, *line_end;
    Log file_log;
    while (reader.ReadLine(&line_start, &line_end)) {
      if (!log_version)
        sscanf(line_start, kFileSignature, &log_version);

      if (log_version < kOldestSupportedVersion) {
        *err = "unable to extract version from build log, perhaps due to "
          "being too old; you must clobber your build output and rebuild";
        return false;
      }

      // If no newline was found in this chunk, read the next.
      if (!line_end)
        continue;

      const char kFieldSeparator = '\t';

      char* start = line_start;
      char* end = (char*)memchr(start, kFieldSeparator, line_end - start);
      if (!end)
        continue;
      *end = 0;

      int start_time = 0, end_time = 0;
      TimeStamp restat_mtime = 0;

      start_time = atoi(start);
      start = end + 1;

      end = (char*)memchr(start, kFieldSeparator, line_end - start);
      if (!end)
        continue;
      *end = 0;
      end_time = atoi(start);
      start = end + 1;

      end = (char*)memchr(start, kFieldSeparator, line_end - start);
      if (!end)
        continue;
      *end = 0;
      restat_mtime = atol(start);
      start = end + 1;

      end = (char*)memchr(start, kFieldSeparator, line_end - start);
      if (!end)
        continue;
      string output = string(start, end - start);
      if (output.empty()) {
        printf("empty output?\n");
      }

      start = end + 1;
      end = line_end;

      // Lines in a file are in temporal order, so later entries should replace
      // earlier ones.
      LogEntry* entry = NULL;
      pair<Log::iterator, bool> insert_result =
          file_log.insert(Log::value_type(output, NULL));
      if (insert_result.second) {
        entry = insert_result.first->second = new LogEntry;
        entry->output.swap(output);
      } else {
        entry = insert_result.first->second;
      }
      entry->start_time = start_time;
      entry->end_time = end_time;
      entry->restat_mtime = restat_mtime;
      if (log_version >= 5) {
        char c = *end; *end = '\0';
        entry->command_hash = (uint64_t)strtoull(start, NULL, 16);
        *end = c;
      } else {
        entry->command_hash = LogEntry::HashCommand(StringPiece(start,
                                                                end - start));
      }

      ++total_entry_count;
    }

    fclose(file);

    if (log_file_number == 0)
      first_file_entry_count = total_entry_count;

    unsigned file_entry_count = file_log.size();
    // But we iterate through the different log files in reverse temporal order, so
    // entries from later files should NOT replace ones from earlier files.
    vector<Log::iterator> to_erase;
    for(Log::iterator i = file_log.begin();
        i != file_log.end(); ++i) {
      pair<Log::iterator, bool> insert_result =
          log_.insert(Log::value_type(i->second->output, i->second));
      if (!insert_result.second)
        to_erase.push_back(i);
    }
    for(vector<Log::iterator>::iterator i = to_erase.begin();
        i != to_erase.end(); ++i) {
      LogEntry* entry = (*i)->second;
      file_log.erase(*i);
      delete entry;
    }
    unsigned unique_file_entry_count = file_entry_count - to_erase.size();
    to_erase.clear();

    float kLogDropRatio = 0.25;
    if (unique_file_entry_count < kLogDropRatio*file_entry_count) {
      pending_log_drops_.push_front(PendingLogDrop());
      pending_log_drops_.back().log_entries_to_save.swap(file_log);
      pending_log_drops_.back().log_file_number = log_file_number;
      printf("I plan to drop log file %s.\n", actual_path.c_str());
    }

    printf("Log file %s has %u total and %u unique entries.\n", actual_path.c_str(), file_entry_count, unique_file_entry_count);
  }

  // Time to rotate the logs?
  unsigned kMaxEntriesPerLog = 10;
  unsigned kMinEntriesToRotate = 1000;
  float kRotationRatio = 0.4;
  if (first_file_entry_count > kMaxEntriesPerLog ||
      (first_file_entry_count > kMinEntriesToRotate &&
       first_file_entry_count > kRotationRatio*log_.size())) {
    needs_rotation_ = true;
  }

  // Decide whether it's time to rebuild the log:
  // - if we're upgrading versions
  // - if it's getting large
  unsigned kMinCompactionEntryCount = 100;
  unsigned kCompactionRatio = 4;
  if (log_version < kCurrentVersion) {
    needs_recompaction_ = true;
  } else if (total_entry_count > kMinCompactionEntryCount &&
             total_entry_count > log_.size() * kCompactionRatio) {
    needs_recompaction_ = true;
  }

  return true;
}

BuildLog::LogEntry* BuildLog::LookupByOutput(const string& path) {
  Log::iterator i = log_.find(path);
  if (i != log_.end())
    return i->second;
  return NULL;
}

// static
void BuildLog::WriteEntry(FILE* f, const LogEntry& entry) {
  fprintf(f, "%d\t%d\t%d\t%s\t%" PRIx64 "\n",
          entry.start_time, entry.end_time, entry.restat_mtime,
          entry.output.c_str(), entry.command_hash);
}

bool BuildLog::DropLogs(const string& path, string* err) {
  for (list<PendingLogDrop>::iterator it = pending_log_drops_.begin();
       it != pending_log_drops_.end(); ++it) {
    string head_log_path = ActualLogPath(path, 0);
    string drop_log_path = ActualLogPath(path, it->log_file_number);

    printf("Dropping log %s, but saving %u entries.\n", drop_log_path.c_str(), static_cast<unsigned>(it->log_entries_to_save.size()));

    if (it->log_entries_to_save.size() != 0 &&
        !WriteLog(&it->log_entries_to_save, head_log_path, err, WRITELOG_APPEND))
      return false;
    
    if (unlink(drop_log_path.c_str()) != 0) {
      *err = strerror(errno);
      return false;
    }

    for (int j = it->log_file_number;; ++j) {
      string to_file = ActualLogPath(path, j);
      string from_file = ActualLogPath(path, j+1);
      if (rename(from_file.c_str(), to_file.c_str()) != 0) {
        if (errno == ENOENT)
          break;
        *err = strerror(errno);
        return false;
      }
    }
    --max_log_file_number_;
  }
  return true;
}


bool BuildLog::Rotate(const string& path, string* err) {
    printf("Rotating logs...\n");
    printf("max log # = %d\n", max_log_file_number_);
    for (int i = max_log_file_number_;i >= 0; --i) {
      string from_file = ActualLogPath(path, i);
      string to_file = ActualLogPath(path, i+1);
      printf("rotating form %s to %s\n", from_file.c_str(), to_file.c_str());
      if (rename(from_file.c_str(), to_file.c_str()) != 0) {
        *err = strerror(errno);
        return false;
      }
    }
    string first_log = ActualLogPath(path, 0);
    FILE* f = fopen(first_log.c_str(), "wb");
    if (!f) {
      *err = strerror(errno);
      return false;
    }
    if (fprintf(f, kFileSignature, kCurrentVersion) < 0) {
      *err = strerror(errno);
      fclose(f);
      return false;
    }
    fclose(f);
    return true;
}

bool BuildLog::Recompact(const string& path, string* err) {
  printf("Recompacting log...\n");
  string temp_path = path + ".recompact";

  if (!WriteLog(&log_, temp_path, err, WRITELOG_TRUNCATE)) {
    return false;
  }

  if (unlink(path.c_str()) < 0) {
    *err = strerror(errno);
    return false;
  }

  if (rename(temp_path.c_str(), path.c_str()) < 0) {
    *err = strerror(errno);
    return false;
  }
  return true;
}

// static
bool BuildLog::WriteLog(Log* log, const string& path, string* err,
                        AppendOrTruncateEnum append_or_truncate) {
  printf("writing %u entries to %s...\n", static_cast<unsigned>(log->size()), path.c_str());
  FILE* f = fopen(path.c_str(),
                  append_or_truncate == WRITELOG_APPEND ? "ab" : "wb");
  if (!f) {
    *err = strerror(errno);
    return false;
  }

  if (fprintf(f, kFileSignature, kCurrentVersion) < 0) {
    *err = strerror(errno);
    fclose(f);
    return false;
  }

  for (Log::iterator i = log->begin(); i != log->end(); ++i) {
    WriteEntry(f, *i->second);
  }

  fclose(f);
  return true;
}

/* remdups4.c
  By Greg Childers and others
  Addition of Bloom filter by apocalypse
  This is a standalone one-pass duplicate relations remover;
      only syntax (a,b:<csv-of-factors>:<csv-of-factors>) is checked and incomplete lines are discarded;
      validity of relations is not tested (nor is polynomial needed).
  Hashing of (a,b) values was changed to accomodate for gnfs projects with huge skews (S.Batalov).

  This version is a filter (stdin, stdout):
    you may redirect stdout to /dev/null and/or
    you may use many input relation files (or pipe from zcat, bzcat).
    However, this needs porting for Windows (use remdups.c instead or get CygWin).

  No makefile needed:
      cc -O3 -o remdups4 remdups4.c

  This program is free software; you can redistribute it and/or
  modify it under the terms of the GNU General Public License
  as published by the Free Software Foundation; either version 2
  of the License, or (at your option) any later version.

  You should have received a copy of the GNU General Public License along
  with this program; see the file COPYING.  If not, write to the Free
  Software Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA
  02111-1307, USA.
*/

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>

typedef unsigned int uint32;
typedef int int32;
typedef unsigned long long uint64;
typedef long long int64;

uint64 NUM_BLOOM_FILTER_INTS;

// Fixed seed for repeatability
const unsigned short SEED[3] = {30450, 30012, 11900};

int NUM_HASHES_FOR_BLOOM_FILTER = 18;
const int HASH_LOOKUP_SIZE = 256;

uint64** BLOOM_FILTER_HASH_LOOKUPS;
typedef int* bloom_filter_t;

void* alloc_or_die(size_t req_memory) {
  void* allocated = malloc(req_memory);
  if (allocated == NULL) {
    fprintf(stderr, "Out of memory");
    exit(-1);
  }
  return allocated;
}

void init_bloom_filter(bloom_filter_t* bloom) {
  if (bloom == NULL) {
    fprintf(stderr, "Unable to initialize bloom filter\n");
    exit(-1);
  }

  // Initialize the table used by the hash functions
  seed48((unsigned short*) SEED);
  uint64 i, j;
  BLOOM_FILTER_HASH_LOOKUPS = alloc_or_die(
    NUM_HASHES_FOR_BLOOM_FILTER * sizeof(uint64*));

  for (i = 0; i < NUM_HASHES_FOR_BLOOM_FILTER; i++) {
    BLOOM_FILTER_HASH_LOOKUPS[i] =
      alloc_or_die(HASH_LOOKUP_SIZE * sizeof(uint64));
    for (j = 0; j < HASH_LOOKUP_SIZE; j++) {
      BLOOM_FILTER_HASH_LOOKUPS[i][j] =
	(lrand48() << 32) | (lrand48() & 0xffffffff);
    }
  }

  // Initialize the bloom filter proper
  *bloom = alloc_or_die(NUM_BLOOM_FILTER_INTS * sizeof(int));

  memset(*bloom, 0, NUM_BLOOM_FILTER_INTS * sizeof(int));
}

int set_bit_on_bloom_filter(bloom_filter_t* bloom, uint64 idx) {
  const int word_size = 8 * sizeof(int);
  uint64 word_idx = idx / word_size;
  int bit_idx = idx % word_size;
  int mask = 1 << (word_size - 1 - bit_idx);
  int ret_val = ((*bloom)[word_idx] & mask) != 0;
  (*bloom)[word_idx] |= mask;
  return ret_val;
}

// Mix the intermediate result and combine with a randomly generated
// number
uint64 lookup_table_hash(uint64 a, uint64 b, uint64 idx) {
  if (idx < 0 || idx > NUM_HASHES_FOR_BLOOM_FILTER) {
    fprintf(stderr, "invalid hash index: %llu", idx);
  }
  uint64 key[2];
  unsigned char* p = (unsigned char*) key;
  key[0] = a;
  key[1] = b;
  uint64 x = 0;
  uint64 i;
  for (i = 0; i < 16; i++) {
    x = ((x << 3) | (x >> 61)) ^ BLOOM_FILTER_HASH_LOOKUPS[idx][p[i]];
  }
  return x;  
}

// return 1 if added, 0 if already exists
int add_to_bloom_filter(bloom_filter_t* bloom, uint64 a, uint64 b) {
  int exists = 1;
  uint64 bf_bits = NUM_BLOOM_FILTER_INTS * 8 * sizeof(int);

  uint64 i;
  for (i = 0; i < NUM_HASHES_FOR_BLOOM_FILTER; i++) {
    uint64 hash = lookup_table_hash(a, b, i) % bf_bits;
    exists &= set_bit_on_bloom_filter(bloom, hash);
  }
  return !exists;
}

int keep_line(bloom_filter_t* bloom, const char* line) {
  const char* comma = strchr(line, ',');
  if (!comma) return -1;
  const char* colon = strchr(comma, ':');
  if (!colon) return -1;
  int64 a = strtoll(line, NULL, 10);
  int64 b = strtoll(comma + 1, NULL, 10);
  return add_to_bloom_filter(bloom, (uint64) a, (uint64) b);
}

const unsigned char BITS_SET_IN_NYBBLE[16] = {
  0, 1, 1, 2, 1, 2, 2, 3, 1, 2, 2, 3, 2, 3, 3, 4,
};

void print_bloom_stats(const bloom_filter_t* bloom) {
  uint64 i;
  char bits_set_in_byte[256];
  for (i = 0; i < 256; i++) {
    bits_set_in_byte[i] =
      BITS_SET_IN_NYBBLE[i >> 4] + BITS_SET_IN_NYBBLE[i & 0xf];
  }
  uint64 bits_set = 0;
  const unsigned char* bf = (const unsigned char*) *bloom;
  for (i = 0; i < NUM_BLOOM_FILTER_INTS * sizeof(int); i++) {
    bits_set += bits_set_in_byte[bf[i]];
  }
  fprintf(stderr, "Bloom Filter with %d hash functions: %llu/%llu bits set.\n",
	  NUM_HASHES_FOR_BLOOM_FILTER, bits_set,
	  NUM_BLOOM_FILTER_INTS * 8 * sizeof(int));
}

int strccnt(const char *s, int c)
{
	const unsigned char *us = (const unsigned char *) s;
	const unsigned char uc = c;
	int n = 0;
	if (!uc) return 1;
	while (*us) if (*us++ == uc) n++;
	return n;
}
int main(int argc, char **argv) {
	char *tmp;
	char buf[512];
	FILE *badfile;
	uint64 numbad=0, numdups=0, numuniq=0;

        if (argc >= 2 && argc <= 3) {
	  uint64 est_rels = strtoull(argv[1], NULL, 10);
	  fprintf(stderr, "Expecting approx. %llu million relations.\n", est_rels);
          if (argc == 3) NUM_HASHES_FOR_BLOOM_FILTER = atoi(argv[2]);
	  NUM_BLOOM_FILTER_INTS =
	      (uint64) ( (est_rels * 125000 / sizeof(int)) * NUM_HASHES_FOR_BLOOM_FILTER /
			0.7); // 125000 = 1000000 / 8
        } else {
	  fprintf(stderr,
		  "\nusage: cat relations.file(s) | %s estimated_rels_in_millions [num_hashes] > out_file \n"
		  "\t estimated_rels is a guess of how many relations to check\n\n",
		  argv[0]);
	  exit(-1);
	}

	badfile = fopen("badrels.txt", "a");
	if (badfile == NULL) {
		fprintf(stderr,"cannot open badfile\n");
		exit(-1);
	}

	bloom_filter_t bloom;
	init_bloom_filter(&bloom);

	while (fgets(buf, sizeof(buf), stdin)) {
		if (buf[0] == '#') {
			//printf("%s", buf);
			continue;
		}
		 
		if (buf[0] == 'N') {
			printf("%s", buf);
			continue;
		}

		  int ret = keep_line(&bloom, buf);
		  if (ret == -1) {  // bad line
		    fprintf(badfile, "%s", buf);
		    numbad++;
		  } else if (ret == 0) {  // duplicate
		    numdups++;
		  } else if (ret == 1) {  // good
		    numuniq++;
		    if(numuniq % 500000 == 0)
		      fprintf(stderr, "\r %.1fM relns \r", numuniq / 1000000.0);
		    for(tmp=buf; *tmp; tmp++)
		      *tmp = tolower(*tmp);  // will compress better
		    printf("%s", buf);
		  }
		
	}
		
        fprintf(stderr,"Found %llu unique, %llu duplicate, and %llu bad relations.\n",numuniq, numdups, numbad);
	  print_bloom_stats(&bloom);
	if(numbad) fprintf(badfile, "\n");	/* usually last reln line is truncated and ends up in the bad bin. We don't want them to stick together */
	fclose(badfile);
	return 0;
}

#include <errno.h>
#include <pthread.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <assert.h>
#include <stdbool.h>

#include "myMalloc.h"

#define MALLOC_COLOR "MALLOC_DEBUG_COLOR"

static bool check_env;
static bool use_color;

/*
 * Mutex to ensure thread safety for the freelist
 */
static pthread_mutex_t mutex;

/*
 * Array of sentinel nodes for the freelists
 */
header freelistSentinels[N_LISTS];

/*
 * Pointer to the second fencepost in the most recently allocated chunk from
 * the OS. Used for coalescing chunks
 */
header * lastFencePost;

/*
 * Pointer to maintain the base of the heap to allow printing based on the
 * distance from the base of the heap
 */ 
void * base;

/*
 * List of chunks allocated by  the OS for printing boundary tags
 */
header * osChunkList [MAX_OS_CHUNKS];
size_t numOsChunks = 0;

/*
 * direct the compiler to run the init function before running main
 * this allows initialization of required globals
 */
static void init (void) __attribute__ ((constructor));

// Helper functions for manipulating pointers to headers
static inline header * get_header_from_offset(void * ptr, ptrdiff_t off);
static inline header * get_left_header(header * h);
static inline header * ptr_to_header(void * p);

// Helper functions for allocating more memory from the OS
static inline void initialize_fencepost(header * fp, size_t left_size);
static inline void insert_os_chunk(header * hdr);
static inline void insert_fenceposts(void * raw_mem, size_t size);
static header * allocate_chunk(size_t size);

// Helper functions for freeing a block
static inline void deallocate_object(void * p);

// Helper functions for allocating a block
static inline header * allocate_object(size_t raw_size);

// Helper functions for verifying that the data structures are structurally 
// valid
static inline header * detect_cycles();
static inline header * verify_pointers();
static inline bool verify_freelist();
static inline header * verify_chunk(header * chunk);
static inline bool verify_tags();

static void init();

static bool isMallocInitialized;

/* Custom helpers */
static inline void remove_block(header * header_block);
static inline void prepend_block(size_t i, header *header_block);
static inline header* search_block(size_t index, size_t actual_size);
static inline header* find_block(size_t actual_size);
static inline size_t get_index_from_actual_size(size_t actual_size);
static inline size_t find_sentinal_index(size_t actual_size);

//random
/**
 * @brief Helper function to retrieve a header pointer from a pointer and an 
 *        offset
 *
 * @param ptr base pointer
 * @param off number of bytes from base pointer where header is located
 *
 * @return a pointer to a header offset bytes from pointer
 */
static inline header * get_header_from_offset(void * ptr, ptrdiff_t off) {
	return (header *)((char *) ptr + off);
}

/**
 * @brief Helper function to get the header to the right of a given header
 *
 * @param h original header
 *
 * @return header to the right of h
 */
header * get_right_header(header * h) {
	return get_header_from_offset(h, get_size(h));
}

/**
 * @brief Helper function to get the header to the left of a given header
 *
 * @param h original header
 *
 * @return header to the right of h
 */
inline static header * get_left_header(header * h) {
  return get_header_from_offset(h, -h->left_size);
}

/**
 * @brief Fenceposts are marked as always allocated and may need to have
 * a left object size to ensure coalescing happens properly
 *
 * @param fp a pointer to the header being used as a fencepost
 * @param left_size the size of the object to the left of the fencepost
 */
inline static void initialize_fencepost(header * fp, size_t left_size) {
	set_state(fp,FENCEPOST);
	set_size(fp, ALLOC_HEADER_SIZE);
	fp->left_size = left_size;
}

/**
 * @brief Helper function to maintain list of chunks from the OS for debugging
 *
 * @param hdr the first fencepost in the chunk allocated by the OS
 */
inline static void insert_os_chunk(header * hdr) {
  if (numOsChunks < MAX_OS_CHUNKS) {
    osChunkList[numOsChunks++] = hdr;
  }
}

/**
 * @brief given a chunk of memory insert fenceposts at the left and 
 * right boundaries of the block to prevent coalescing outside of the
 * block
 *
 * @param raw_mem a void pointer to the memory chunk to initialize
 * @param size the size of the allocated chunk
 */
inline static void insert_fenceposts(void * raw_mem, size_t size) {
  // Convert to char * before performing operations
  char * mem = (char *) raw_mem;

  // Insert a fencepost at the left edge of the block
  header * leftFencePost = (header *) mem;
  initialize_fencepost(leftFencePost, ALLOC_HEADER_SIZE);

  // Insert a fencepost at the right edge of the block
  header * rightFencePost = get_header_from_offset(mem, size - ALLOC_HEADER_SIZE);
  initialize_fencepost(rightFencePost, size - 2 * ALLOC_HEADER_SIZE);
}

/**
 * @brief Allocate another chunk from the OS and prepare to insert it
 * into the free list
 *
 * @param size The size to allocate from the OS
 *
 * @return A pointer to the allocable block in the chunk (just after the 
 * first fencpost)
 */
static header * allocate_chunk(size_t size) {
  void * mem = sbrk(size);
  
  insert_fenceposts(mem, size);
  header * hdr = (header *) ((char *)mem + ALLOC_HEADER_SIZE);
  set_state(hdr, UNALLOCATED);
  set_size(hdr, size - 2 * ALLOC_HEADER_SIZE);
  hdr->left_size = ALLOC_HEADER_SIZE;
  return hdr;
}


/**
 * @brief Helper allocate an object given a raw request size from the user
 *
 * @param raw_size number of bytes the user needs
 *
 * @return A block satisfying the user's request
 */


static inline header *allocate_object(size_t raw_size) {
  /* An allocation of 0 bytes should return the NULL pointer for determinism */
  if (raw_size == 0) {
    return NULL;
  }

   /*
   * Calculate the actual size needed 
   */

  size_t rounded_size = (raw_size + 7) & ~7;
  size_t actual_size = ALLOC_HEADER_SIZE + rounded_size;
  actual_size = actual_size > sizeof(header) ? actual_size : sizeof(header);

  /*
   * Find the appropriate free list to look for a block to allocate 
   * (recall that the block size per each list is based on the rounded 
   * request size, not including the metadata) size of the head
   */

  /*
   * Find the block to allocate provided actual_size 
   */

   header* block = find_block(actual_size);

   while (block == NULL) {
     header * new_chunk = allocate_chunk(ARENA_SIZE);
     header * left_fencePost = get_left_header(new_chunk);

     if (get_left_header(left_fencePost) == lastFencePost) {
        /* If the last block is allocated we just delete the last fenceposts
         * and make a new header adding new chunk to a free list 
         */
        header *last_block = get_left_header(lastFencePost);
        if (get_state(last_block) == ALLOCATED) {
          header *bigger_new_chunk = lastFencePost;
          set_state(bigger_new_chunk, UNALLOCATED);
          set_size(bigger_new_chunk, 2 * get_size(bigger_new_chunk) + get_size(new_chunk));
          get_right_header(new_chunk)->left_size = get_size(bigger_new_chunk);

          /* Move into last free list */
          prepend_block(N_LISTS - 1, bigger_new_chunk);
          lastFencePost = get_right_header(new_chunk);
        } else {
          /* The last block is unallocated */
         size_t old_index = get_index_from_actual_size(get_size(last_block));
         set_size(last_block, get_size(last_block) + 2 * get_size(lastFencePost) + get_size(new_chunk));
         get_right_header(new_chunk)->left_size = get_size(last_block);

         if (get_index_from_actual_size(get_size(last_block)) != old_index) {
           remove_block(last_block);
           prepend_block(get_index_from_actual_size(get_size(last_block)), last_block);
         }
        }
     } else {
        insert_os_chunk(left_fencePost);
        prepend_block(N_LISTS - 1, new_chunk);
        lastFencePost = get_right_header(new_chunk);
     }

      block = find_block(actual_size);
   }

   /* Case: Don't need to split and just return block directly */
    if (get_size(block) == actual_size || ((get_size(block) > actual_size) && (get_size(block) - actual_size <= ALLOC_HEADER_SIZE)))  {
       /* Set state to allocated */
       remove_block(block);
       set_state(block, ALLOCATED);
       return (header *)((char *) block + ALLOC_HEADER_SIZE);
    } else {
          /* We need to split the block, allocate the right side */
          size_t remainder = get_size(block) - actual_size; 
          /* Create header at the allocation location */
          header * split = get_header_from_offset(block, (ptrdiff_t)remainder);

          set_size(split, actual_size);

          set_state(split, ALLOCATED);
          /* set the left of the alloc block */
          split->left_size = remainder;

          header *right = get_right_header(split);

          right->left_size = get_size(split);

          /* We must update the size of the remainder now */
          set_size(block, remainder);

          /*
           * When splitting a block, if the size of the remaining block is no longer appropriate for the current list, 
           * the remainder block should be removed and inserted into the appropriate free list.
           */
         
          /* Check if we need to move the remainder or not */
          if (get_index_from_actual_size(get_size(block)) < N_LISTS - 1) {
            remove_block(block);
            prepend_block(get_index_from_actual_size(get_size(block)), block);
          } 
                    
          return (header *)((char *) split + ALLOC_HEADER_SIZE);
        } 
}


/*
 * Find index given total size
 */

static inline size_t get_index_from_actual_size(size_t actual_size) {
  return ((actual_size - ALLOC_HEADER_SIZE ) / 8) - 1 <= N_LISTS - 1 ? ((actual_size - ALLOC_HEADER_SIZE) / 8) - 1 : N_LISTS - 1;
}



static inline void prepend_block(size_t i, header *header_block) {
   header *sentinal = &freelistSentinels[i];
   header *next = sentinal->next;

   sentinal->next = header_block;
   header_block->prev = sentinal;
   next->prev = header_block;
   header_block->next = next;
}

static inline void remove_block(header * header_block) {
  /* Disconnect the adjacent nodes */
   header_block->prev->next = header_block->next;
   header_block->next->prev = header_block->prev;
  /* Disconnect current node */
   header_block->prev = NULL;
   header_block->next = NULL;
}


static inline header* search_block(size_t index, size_t actual_size) {
  if (index >= N_LISTS - 1) {
     header* current = &freelistSentinels[index];
     header *first = current;
     current = current->next;
       while (get_size(current) < actual_size) {
         current = current->next;
         if (current == first) {
          return NULL;
         } 
       }
       /* Returns current once found */
      return current;
  } else {
    return (&freelistSentinels[index])->next;
  }
  /* need to consider create new chunk */
}

static inline header* find_block(size_t actual_size) {
  /* Start from the index we predict and cycle through till we have non empty list */
  for (size_t i = get_index_from_actual_size(actual_size); i <= N_LISTS - 1; i++) {
    header *block = search_block(i, actual_size);
    if (block == NULL || block != block->next ){
      return block;
    }
  } 
}

static inline void combine_inplace(header *a, header *b) {
  header *b_next = b->next;
  b_next->prev = a;
  a->next = b_next;
  header *b_prev = b->prev;
  b_prev->next = a;
  a->prev = b_prev;
}


/**
 * @brief Helper to get the header from a pointer allocated with malloc
 *
 * @param p pointer to the data region of the block
 *
 * @return A pointer to the header of the block
 */
static inline header * ptr_to_header(void * p) {
  return (header *)((char *) p - ALLOC_HEADER_SIZE); //sizeof(header));
}

/**
 * @brief Helper to manage deallocation of a pointer returned by the user
 *
 * @param p The pointer returned to the user by a call to malloc
 */
static inline void deallocate_object(void * p) {
  // TODO implement deallocation
  if (p == NULL) {
    return;
  }
  header * block = ptr_to_header(p);
  size_t actual_size = get_size(block);

  if (get_state(block) == UNALLOCATED) {
    puts("test_double_free: ../myMalloc.c:577: deallocate_object: Assertion `false' failed.");
    abort();
  }


  header *left_block = get_left_header(block);
  header *right_block = get_right_header(block);

  size_t right_index = get_index_from_actual_size(get_size(right_block));
  size_t left_index = get_index_from_actual_size(get_size(left_block));

  /* Neither right or left are unallocated */
  size_t index = get_index_from_actual_size(actual_size);

 
  if (get_state(left_block) == UNALLOCATED && get_state(right_block) == UNALLOCATED) {
    /* Combine all three blocks together. */
    set_state(block, UNALLOCATED);
    size_t new_size = get_size(left_block) + actual_size + get_size(right_block);
    set_size(left_block, new_size);
    get_right_header(right_block)->left_size = new_size;
 

    size_t index_new = get_index_from_actual_size(new_size);
    remove_block(right_block);
    if (left_index != N_LISTS - 1) {
      remove_block(left_block);
      prepend_block(index_new, left_block);
    }

  } else if (get_state(right_block) == UNALLOCATED) {
      size_t new_size = actual_size + get_size(right_block);
      /* Update the size */
      set_state(block, UNALLOCATED);
      set_size(block, new_size);
      header *right_right = get_right_header(right_block);
      right_right->left_size = new_size;
      
      right_block->next->prev = block;
      right_block->prev->next = block;
      block->next = right_block->next;
      block->prev = right_block->prev;

      size_t index_new = get_index_from_actual_size(new_size);

      if (right_index != N_LISTS - 1 ) {
        remove_block(block);
        prepend_block(index_new, block);
      } 
  
  } else if (get_state(left_block) == UNALLOCATED) {
    size_t new_size = get_size(left_block) + actual_size;

    set_size(left_block, new_size);
    right_block->left_size = new_size;
    size_t index_new = get_index_from_actual_size(new_size);
    if (left_index != N_LISTS - 1) {
      remove_block(left_block);
      prepend_block(index_new, left_block);
    }
  } else {
      set_state(block, UNALLOCATED);
      prepend_block(index, block);
  }


}

/**
 * @brief Helper to detect cycles in the free list
 * https://en.wikipedia.org/wiki/Cycle_detection#Floyd's_Tortoise_and_Hare
 *
 * @return One of the nodes in the cycle or NULL if no cycle is present
 */
static inline header * detect_cycles() {
  for (int i = 0; i < N_LISTS; i++) {
    header * freelist = &freelistSentinels[i];
    for (header * slow = freelist->next, * fast = freelist->next->next; 
         fast != freelist; 
         slow = slow->next, fast = fast->next->next) {
      if (slow == fast) {
        return slow;
      }
    }
  }
  return NULL;
}

/**
 * @brief Helper to verify that there are no unlinked previous or next pointers
 *        in the free list
 *
 * @return A node whose previous and next pointers are incorrect or NULL if no
 *         such node exists
 */
static inline header * verify_pointers() {
  for (int i = 0; i < N_LISTS; i++) {
    header * freelist = &freelistSentinels[i];
    for (header * cur = freelist->next; cur != freelist; cur = cur->next) {
      if (cur->next->prev != cur || cur->prev->next != cur) {
        return cur;
      }
    }
  }
  return NULL;
}

/**
 * @brief Verify the structure of the free list is correct by checkin for 
 *        cycles and misdirected pointers
 *
 * @return true if the list is valid
 */
static inline bool verify_freelist() {
  header * cycle = detect_cycles();
  if (cycle != NULL) {
    fprintf(stderr, "Cycle Detected\n");
    print_sublist(print_object, cycle->next, cycle);
    return false;
  }

  header * invalid = verify_pointers();
  if (invalid != NULL) {
    fprintf(stderr, "Invalid pointers\n");
    print_object(invalid);
    return false;
  }

  return true;
}

/**
 * @brief Helper to verify that the sizes in a chunk from the OS are correct
 *        and that allocated node's canary values are correct
 *
 * @param chunk AREA_SIZE chunk allocated from the OS
 *
 * @return a pointer to an invalid header or NULL if all header's are valid
 */
static inline header * verify_chunk(header * chunk) {
	if (get_state(chunk) != FENCEPOST) {
		fprintf(stderr, "Invalid fencepost\n");
		print_object(chunk);
		return chunk;
	}
	
	for (; get_state(chunk) != FENCEPOST; chunk = get_right_header(chunk)) {
		if (get_size(chunk)  != get_right_header(chunk)->left_size) {
			fprintf(stderr, "Invalid sizes\n");
			print_object(chunk);
			return chunk;
		}
	}
	
	return NULL;
}

/**
 * @brief For each chunk allocated by the OS verify that the boundary tags
 *        are consistent
 *
 * @return true if the boundary tags are valid
 */
static inline bool verify_tags() {
  for (size_t i = 0; i < numOsChunks; i++) {
    header * invalid = verify_chunk(osChunkList[i]);
    if (invalid != NULL) {
      return invalid;
    }
  }

  return NULL;
}

/**
 * @brief Initialize mutex lock and prepare an initial chunk of memory for allocation
 */
static void init() {
  // Initialize mutex for thread safety
  pthread_mutex_init(&mutex, NULL);

#ifdef DEBUG
  // Manually set printf buffer so it won't call malloc when debugging the allocator
  setvbuf(stdout, NULL, _IONBF, 0);
#endif // DEBUG

  // Allocate the first chunk from the OS
  header * block = allocate_chunk(ARENA_SIZE);

  header * prevFencePost = get_header_from_offset(block, -ALLOC_HEADER_SIZE);
  insert_os_chunk(prevFencePost);

  lastFencePost = get_header_from_offset(block, get_size(block));

  // Set the base pointer to the beginning of the first fencepost in the first
  // chunk from the OS
  base = ((char *) block) - ALLOC_HEADER_SIZE; //sizeof(header);

  // Initialize freelist sentinels
  for (int i = 0; i < N_LISTS; i++) {
    header * freelist = &freelistSentinels[i];
    freelist->next = freelist;
    freelist->prev = freelist;
  }

  // Insert first chunk into the free list
  header * freelist = &freelistSentinels[N_LISTS - 1];
  freelist->next = block;
  freelist->prev = block;
  block->next = freelist;
  block->prev = freelist;
}

/* 
 * External interface
 */
void * my_malloc(size_t size) {
  pthread_mutex_lock(&mutex);
  header * hdr = allocate_object(size); 
  pthread_mutex_unlock(&mutex);
  return hdr;
}

void * my_calloc(size_t nmemb, size_t size) {
  return memset(my_malloc(size * nmemb), 0, size * nmemb);
}

void * my_realloc(void * ptr, size_t size) {
  void * mem = my_malloc(size);
  memcpy(mem, ptr, size);
  my_free(ptr);
  return mem; 
}

void my_free(void * p) {
  pthread_mutex_lock(&mutex);
  deallocate_object(p);
  pthread_mutex_unlock(&mutex);
}

bool verify() {
  return verify_freelist() && verify_tags();
}

/**
 * @brief Print just the block's size
 *
 * @param block The block to print
 */
void basic_print(header * block) {
	printf("[%zd] -> ", get_size(block));
}

/**
 * @brief Print just the block's size
 *
 * @param block The block to print
 */
void print_list(header * block) {
	printf("[%zd]\n", get_size(block));
}

/**
 * @brief return a string representing the allocation status
 *
 * @param allocated The allocation status field
 *
 * @return A string representing the allocation status
 */
static inline const char * allocated_to_string(char allocated) {
  switch(allocated) {
    case UNALLOCATED: 
      return "false";
    case ALLOCATED:
      return "true";
    case FENCEPOST:
      return "fencepost";
  }
  assert(false);
}

static bool check_color() {
  if (!check_env) {
    // genenv allows accessing environment varibles
    const char * var = getenv(MALLOC_COLOR);
    use_color = var != NULL && !strcmp(var, "1337_CoLoRs");
    check_env = true;
  }
  return use_color;
}

/**
 * @brief Change the tty color based on the block's allocation status
 *
 * @param block The block to print the allocation status of
 */
static void print_color(header * block) {
  if (!check_color()) {
    return;
  }

  switch(get_state(block)) {
    case UNALLOCATED:
      printf("\033[0;32m");
      break;
    case ALLOCATED:
      printf("\033[0;34m");
      break;
    case FENCEPOST:
      printf("\033[0;33m");
      break;
  }
}

static void clear_color() {
  if (check_color()) {
    printf("\033[0;0m");
  }
}

static inline bool is_sentinel(void * p) {
  for (int i = 0; i < N_LISTS; i++) {
    if (&freelistSentinels[i] == p) {
      return true;
    }
  }
  return false;
}

/**
 * @brief Print the free list pointers if RELATIVE_POINTERS is set to true
 * then print the pointers as an offset from the base of the heap. This allows
 * for determinism in testing. 
 * (due to ASLR https://en.wikipedia.org/wiki/Address_space_layout_randomization#Linux)
 *
 * @param p The pointer to print
 */
void print_pointer(void * p) {
  if (is_sentinel(p)) {
    printf("SENTINEL");
  } else {
    if (RELATIVE_POINTERS) {
      printf("%04zd", p - base);
    } else {
      printf("%p", p);
    }
  }
}

/**
 * @brief Verbose printing of all of the metadata fields of each block
 *
 * @param block The block to print
 */
void print_object(header * block) {
  print_color(block);

  printf("[\n");
  printf("\taddr: ");
  print_pointer(block);
  puts("");
  printf("\tsize: %zd\n", get_size(block) );
  printf("\tleft_size: %zd\n", block->left_size);
  printf("\tallocated: %s\n", allocated_to_string(get_state(block)));
  if (!get_state(block)) {
    printf("\tprev: ");
    print_pointer(block->prev);
    puts("");

    printf("\tnext: ");
    print_pointer(block->next);
    puts("");
  }
  printf("]\n");

  clear_color();
}

/**
 * @brief Simple printer that just prints the allocation status of each block
 *
 * @param block The block to print
 */
void print_status(header * block) {
  print_color(block);
  switch(get_state(block)) {
    case UNALLOCATED:
      printf("[U]");
      break;
    case ALLOCATED:
      printf("[A]");
      break;
    case FENCEPOST:
      printf("[F]");
      break;
  }
  clear_color();
}

/*
static void print_bitmap() {
  printf("bitmap: [");
  for(int i = 0; i < N_LISTS; i++) {
    if ((freelist_bitmap[i >> 3] >> (i & 7)) & 1) {
      printf("\033[32m#\033[0m");
    } else {
      printf("\033[34m_\033[0m");
    }
    if (i % 8 == 7) {
      printf(" ");
    }
  }
  puts("]");
}
*/

/**
 * @brief Print a linked list between two nodes using a provided print function
 *
 * @param pf Function to perform the actual printing
 * @param start Node to start printing at
 * @param end Node to stop printing at
 */
void print_sublist(printFormatter pf, header * start, header * end) {  
  for (header * cur = start; cur != end; cur = cur->next) {
    pf(cur); 
  }
}

/**
 * @brief print the full freelist
 *
 * @param pf Function to perform the header printing
 */
void freelist_print(printFormatter pf) {
  if (!pf) {
    return;
  }

  for (size_t i = 0; i < N_LISTS; i++) {
    header * freelist = &freelistSentinels[i];
    if (freelist->next != freelist) {
      printf("L%zu: ", i);
      print_sublist(pf, freelist->next, freelist);
      puts("");
    }
    fflush(stdout);
  }
}

/**
 * @brief print the boundary tags from each chunk from the OS
 *
 * @param pf Function to perform the header printing
 */
void tags_print(printFormatter pf) {
  if (!pf) {
    return;
  }

  for (size_t i = 0; i < numOsChunks; i++) {
    header * chunk = osChunkList[i];
    pf(chunk);
    for (chunk = get_right_header(chunk);
         get_state(chunk) != FENCEPOST; 
         chunk = get_right_header(chunk)) {
        pf(chunk);
    }
    pf(chunk);
    fflush(stdout);
  }
}

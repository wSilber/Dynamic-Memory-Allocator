/*
 ******************************************************************************
 *                               mm.c                                         *
 *           64-bit struct-based segregated free list memory allocator        *
 *           with coalesce functionality, removed footers, and min            *
 *           block size of 16 bytes                                           *
 *                                                                            *
 *                 CSE 361: Introduction to Computer Systems                  *
 *                                                                            *
 *  ************************************************************************  *
 *                     insert your documentation here. :)                     *
 *                                                                            *
 *  William Silberstein - 473590                                              *
 *  wsilberstein@wustl.edu                                                    *
 *                                                                            *
 *                                                                            *
 *                                                                            *
 *  ************************************************************************  *
 *  ** ADVICE FOR STUDENTS. **                                                *
 *  Step 0: Please read the writeup!                                          *
 *  Step 1: Write your heap checker. Write. Heap. checker.                    *
 *  Step 2: Place your contracts / debugging assert statements.               *
 *  Good luck, and have fun!                                                  *
 *                                                                            *
 ******************************************************************************
 */

/* Do not change the following! */

#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <stdbool.h>
#include <stddef.h>
#include <assert.h>
#include <stddef.h>

#include "mm.h"
#include "memlib.h"

#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif /* def DRIVER */

/* You can change anything from here onward */

/*
 * If DEBUG is defined, enable printing on dbg_printf and contracts.
 * Debugging macros, with names beginning "dbg_" are allowed.
 * You may not define any other macros having arguments.
 */
//#define DEBUG // uncomment this line to enable debugging

#ifdef DEBUG
/* When debugging is enabled, these form aliases to useful functions */
#define dbg_printf(...) printf(__VA_ARGS__)
#define dbg_requires(...) assert(__VA_ARGS__)
#define dbg_assert(...) assert(__VA_ARGS__)
#define dbg_ensures(...) assert(__VA_ARGS__)
#else
/* When debugging is disnabled, no code gets generated for these */
#define dbg_printf(...)
#define dbg_requires(...)
#define dbg_assert(...)
#define dbg_ensures(...)
#endif

/* Basic constants */
typedef uint64_t word_t;
static const size_t wsize = sizeof(word_t);   // word and header size (bytes)
static const size_t dsize = 2*sizeof(word_t);       // double word size (bytes)
static const size_t min_block_size = 2*sizeof(word_t); // Minimum block size
static const size_t chunksize = (1 << 12);    // requires (chunksize % 16 == 0)

/* Masks */
static const word_t alloc_mask = 0x1;
static const word_t size_mask = ~(word_t)0xF;
static const word_t SB_MASK = 0x4;
static const word_t SB_HEADER_MASK = 0xFFFFFFFFFFFFFFF8;

// Block struct
typedef struct block
{
    /* Header contains size + allocation flag */
    word_t header;

    /* Use union for block info since free blocks will only contain
     * prev and next block pointers while allocated blocks will only
     * contain the payload.
     */
    union {
	char payload[0];
        struct {
            struct block* prev;
            struct block* next;
        };
        word_t p_f;
    };
} block_t;

/* Global variables */
static block_t *heap_start = NULL;

bool mm_checkheap(int lineno);

/* Function prototypes for internal helper routines */
static block_t *extend_heap(size_t size);
static void place(block_t *block, size_t asize);
static block_t *find_fit(size_t asize);
static block_t *coalesce(block_t *block);

static size_t max(size_t x, size_t y);
static size_t round_up(size_t size, size_t n);
static word_t pack(size_t size, bool alloc, bool prev_alloc);

static size_t extract_size(word_t header);
static size_t get_size(block_t *block);
static size_t get_payload_size(block_t *block);

static bool extract_alloc(word_t header);
static bool get_alloc(block_t *block);
static bool extract_prev_alloc(word_t header);
static bool get_prev_alloc(block_t *block);

static void write_header(block_t *block, 
		         size_t size, 
			 bool alloc, 
			 bool prev_alloc);
static void write_footer(block_t *block, size_t size, bool alloc);

static block_t *payload_to_header(void *bp);
static void *header_to_payload(block_t *block);

static block_t *find_next(block_t *block);
static word_t *find_prev_footer(block_t *block);
static block_t *find_prev(block_t *block);

/* Added Functions And Variables */
static block_t *freeList_start = NULL;

/* Segregated list sizes */
#define SLIST_SIZE 7
#define SIZE_1 16
#define SIZE_2 32
#define SIZE_3 64
#define SIZE_4 128
#define SIZE_5 256
#define SIZE_6 512

/* Segregated list functions */
static block_t *sList[SLIST_SIZE];
static void add_free_block(block_t *block);
static void remove_free_block(block_t *block);
static int block_to_sList(block_t *block);
static int size_to_sList(size_t size);
static bool is_free_alloc(block_t *block);
static word_t pack_16(block_t *block, bool alloc, bool prev_alloc);
static bool get_16_alloc(block_t *block);
static void set_prev(block_t *block, block_t *block_prev);
static void set_next(block_t *block, block_t *block_next);
static block_t *get_next_free(block_t *block);
static block_t *get_prev_free(block_t *block);
static void write_header_16(block_t *block, 
		            block_t *next_block, 
			    bool alloc, 
			    bool prev_alloc);
static void write_p_f(block_t *block, block_t *prev_block, bool alloc);
static bool get_16_alloc_h(word_t header);

/* Check heap function */
static int count_free_blocks_in_heap();
static int count_free_blocks_in_sList();

/* Debug functions */
static void print_free_blocks();
static void print_block(block_t *block);
static void print_heap();

/* N-Fit defintions */
#define MAX_INT 0x7fffffff
#define N_SIZE 70

/* Block shift defintions */
#define PREV_ALLOC_SHIFT 1
#define SMALL_BLOCK_SHIFT 2

/* Check heap error codes */
#define NEIGHBOR_FREE_ERROR -1
#define ALLOC_MISMATCH_ERROR -2
#define ALLOC_IN_SLIST_ERROR -3
#define HEADER_FOOTER_MISMATCH_ERROR -4
#define SLIST_MISMATCH_ERROR -5
#define BLOCK_SIZE_ALLOC_ERROR -6

/*
 * Initializes the heap
 */
bool mm_init(void)
{
    // Create the initial empty heap
    word_t *start = (word_t *)(mem_sbrk(2*wsize));

    if (start == (void *)-1)
    {
        return false;
    }

    start[0] = pack(0, true, true); // Prologue footer
    start[1] = pack(0, true, true); // Epilogue header

    // Heap starts with first "block header", currently the epilogue footer
    heap_start = (block_t *) &(start[1]);
    
    int i = 0;
    for(; i < SLIST_SIZE; i++) {
	sList[i] = NULL;
    }    


    // Free list starts at the first block since it will initially be free
    freeList_start = NULL;

    // Extend the empty heap with a free block of chunksize bytes
    if (extend_heap(chunksize) == NULL)
    {
        return false;
    }
    return true;
}

/*
 * Allocates a block of an arbitrary size.
 * Returns the block address if successful or NULL if unsuccessful
 */
void *malloc(size_t size)
{
    dbg_requires(mm_checkheap(__LINE__));
    size_t asize;      // Adjusted block size
    size_t extendsize; // Amount to extend heap if no fit is found
    block_t *block;
    void *bp = NULL;

    if (heap_start == NULL) // Initialize heap if it isn't initialized
    {
        mm_init();
    }

    if (size == 0) // Ignore spurious request
    {
        dbg_ensures(mm_checkheap(__LINE__));
        return bp;
    }

    // Round block size to nearest double word
    asize = round_up(size + wsize, dsize);

    if(asize < min_block_size)
            asize = min_block_size;
    
    // Search the free list for a fit
    block = find_fit(asize);


    // If no fit is found, request more memory, and then and place the block
    if (block == NULL)
    {
        extendsize = max(asize, chunksize);
        block = extend_heap(extendsize);
        if (block == NULL) // extend_heap returns an error
        {
            return bp;
        }

    }

    place(block, asize);
    bp = header_to_payload(block);
    dbg_ensures(mm_checkheap(__LINE__));
    return bp;
}

/*
 * free: Frees the block from the given pointer location.
 *       Returns NULL if the block does not exist
 */
void free(void *bp)
{
    if (bp == NULL)
    {
        return;
    }

    block_t *block = payload_to_header(bp);
    size_t size = get_size(block);
    write_header(block, size, false, get_prev_alloc(block));
    write_footer(block, size, false);

    coalesce(block);
}

/*
 * Attemps to resize an allocated block given a pointer to a block and a size
 * Returns the block if successful or NULL if unsuccessful
 */
void *realloc(void *ptr, size_t size)
{
    block_t *block = payload_to_header(ptr);
    size_t copysize;
    void *newptr;

    // If size == 0, then free block and return NULL
    if (size == 0)
    {
        free(ptr);
        return NULL;
    }

    // If ptr is NULL, then equivalent to malloc
    if (ptr == NULL)
    {
        return malloc(size);
    }

    // Otherwise, proceed with reallocation
    newptr = malloc(size);

    // If malloc fails, the original block is left untouched
    if (newptr == NULL)
    {
        return NULL;
    }

    // Copy the old data
    copysize = get_payload_size(block); // gets size of old payload
    if(size < copysize)
    {
        copysize = size;
    }
    memcpy(newptr, ptr, copysize);

    // Free the old block
    free(ptr);

    return newptr;
}

/*
 * Allocates a block of arbitrary size and initializes all of the bytes to 0.
 * Returns the block if successful or NULL if a block could not be allocated
 */
void *calloc(size_t elements, size_t size)
{
    void *bp;
    size_t asize = elements * size;

    if (asize/elements != size)
    {
        // Multiplication overflowed
        return NULL;
    }

    bp = malloc(asize);
    if (bp == NULL)
    {
        return NULL;
    }

    // Initialize all bits to 0
    memset(bp, 0, asize);

    return bp;
}

/******** The remaining content below are helper and debug routines ********/

/*
 * Extends the heap by an arbitrary size.
 */
static block_t *extend_heap(size_t size)
{
    void *bp;
    
    // Allocate an even number of words to maintain alignment
    size = round_up(size, dsize);
    if ((bp = mem_sbrk(size)) == (void *)-1)
    {
        return NULL;
    }

    // Initialize free block header/footer
    block_t *block = payload_to_header(bp);
    write_header(block, size, false, get_prev_alloc(block));
    write_footer(block, size, false);

    // Create new epilogue header
    block_t *block_next = find_next(block);
    write_header(block_next, 0, true, false);

    return coalesce(block);
}

/*
 * Adds a free block to the free block list
 */
static void add_free_block(block_t *block) {

    set_next(block, NULL);
    set_prev(block, NULL);

    int index = block_to_sList(block);

    // No block in the sList
    if(!sList[index]) {
	sList[index] = block;
    } else {
	set_next(block, sList[index]);
	set_prev(sList[index], block);
	sList[index] = block;
    }
}

/*
 * Removes a free block from the free block list
 */
static void remove_free_block(block_t *block) {
    int index = block_to_sList(block);
    
    // Nothing in free list
    if(!sList[index]) {
        return;
    }
    
    // Block is the start of the free list
    if(!get_prev_free(block)) {
        
	// Block is only block in free list
        if(!get_next_free(sList[index])) {
            sList[index] = NULL;
        
	// Block is not only block in free list
        } else {
            set_prev(get_next_free(block), NULL);
            sList[index] = get_next_free(block);
        }

    // Block is not the first block in the list
    } else {

        // Block is the last block in the free list
        if(!get_next_free(block)) {
            set_next(get_prev_free(block), NULL);
            set_prev(block, NULL);

        // Block is in the middle of the list
        } else {
            set_next(get_prev_free(block), get_next_free(block));
            set_prev(get_next_free(block), get_prev_free(block));
        }
    }
   
    // Set the block pointers to NULL
    set_prev(block, NULL);
    set_next(block, NULL);

}

/*
 * Joins together free blocks in order to free up space
 */
static block_t *coalesce(block_t * block)
{

    // Get next block
    block_t *next_block = find_next(block);

    // Get size of blocks blocks
    size_t block_size = get_size(block);
    size_t next_block_size = get_size(next_block);

    // Get if the previous and next block are allocated
    bool is_prev_block = get_prev_alloc(block);
    bool is_next_block = get_alloc(next_block);

    // Case 1: Surrounded by allocated blocks -> unallocate block
    if(is_prev_block && is_next_block) {
        write_header(block, block_size, false, true);
        write_header(next_block, next_block_size, true, false);
        add_free_block(block);
        return block;

    // Case 2: Has allocated previous block.
    // Combine previous block with current block
    } else if(is_prev_block && !is_next_block) {

        // Remove next block from the free list
        remove_free_block(next_block);

        // Size of new block equals size of block + size of next block
        size_t size = block_size + next_block_size;

        // Write header and footer for non allocated block
        write_header(block, size, false, true);
        write_footer(block, size, false);

        // Update header of next block
        next_block = find_next(block);
        next_block_size = get_size(next_block);
        write_header(next_block, next_block_size, true, false);

    // Case 3: Has allocated next block
    } else if(!is_prev_block && is_next_block) {

        // Get prev block and size
        block_t *prev_block = find_prev(block);
        size_t prev_block_size = get_size(prev_block);

        // Remove previous block from the free list
        remove_free_block(prev_block);

        // Size of new block equals size of block + size of previous block
        size_t size = block_size + prev_block_size;

        // Write header / footer for block and next block
        write_header(prev_block, size, false, true);
        write_footer(prev_block, size, false);

        write_header(next_block, next_block_size, true, false);
        block = prev_block;

    // Case 4: Surrounded by free blocks
    } else if(!is_prev_block && !is_next_block){

        // Get prev block and size
        block_t *prev_block = find_prev(block);
        size_t prev_block_size = get_size(prev_block);

        // Remove both the previous and next block
        remove_free_block(prev_block);
        remove_free_block(next_block);

        // Size of new block equals size of surrounding neighbors.
        size_t size = block_size + prev_block_size + next_block_size;

        // Write header / footer for block
        write_header(prev_block, size, false, true);
        write_footer(prev_block, size, false);

        // Update next block's header
        next_block = find_next(prev_block);
        next_block_size = get_size(next_block);
        write_header(next_block, next_block_size, true, false);

        block = prev_block;

    }

    // Add the new block to the free list and return the block
    add_free_block(block);
    //print_block(next_block);
    return block;
}

/*
 * place: Places a block of size asize into memory. 
 * Splits the block if the block is bigger than needed
 */
static void place(block_t *block, size_t asize)
{
    size_t csize = get_size(block);
block_t *next_block = get_next_free(block);
    
    // Block needs to be split
    if ((csize - asize) >= min_block_size)
    {
        block_t *block_next;
        block_t *block_prev = get_prev_free(block);

        // Remove current block from free list and set headers
        remove_free_block(block);
        write_header(block, asize, true, get_prev_alloc(block));
        write_footer(block, asize, true);

        // Set the rest of the split block as free and add it to the free list
        block_next = find_next(block);
        if(csize-asize == SIZE_1) {
	    write_header_16(block_next, block_prev, false, true);
	    write_p_f(block_next, block_prev, false);
	} else {
	    write_header(block_next, csize-asize, false, true);
            write_footer(block_next, csize-asize, false);
	}	
        add_free_block(block_next);
    }

    // Block does not need to be split.
    // Remove block from free list and allocate it
    else
    {
        // Add headers to new block and next block and remove the block
	// from the free list
	if(asize == SIZE_1) {
	    block->header = (word_t) next_block | 
		            (1 << SMALL_BLOCK_SHIFT) | 
			    (1 << PREV_ALLOC_SHIFT) | 
			    1;
	} else {
	    write_header(block, csize, true, get_prev_alloc(block));
	}

        write_header(find_next(block), 
	             get_size(find_next(block)), 
		     get_alloc(find_next(block)), 
		     true);
        remove_free_block(block);
    }
}

/*
 * find_fit: Scans the first n free blocks of valid size.
 *           Returns smallest block if one was found
 */
static block_t *find_fit(size_t asize)
{
    block_t *block;
    block_t *best_block = NULL;
    size_t smallest_size = MAX_INT;
    size_t block_size = 0;
    int n = N_SIZE;
    int index = size_to_sList(asize);

    /* Loop through all of the segregated lists with valid sizes */ 
    for(;index < SLIST_SIZE; index++) {
        for (block = sList[index]; block != NULL && n > 0;
	     block = block->next) {

            block_size = get_size(block);

            // Found a free block with a valid size
            if (asize <= block_size) {
                n--;

                // Return the block if found a perfect size
                if(block_size == asize) {
                    return block;
                }

                // Set block becomes best block if current free block
	        // smaller than current best block
                if(block_size < smallest_size) {
                    best_block = block;
                    smallest_size = get_size(block);
                }
            }
        }
    }
    
   return best_block;
}

/*
 * mm_checkheap: Scans the entire heap and all segregated lists and checks
 *               for the following invariants in every block. Returns true
 *               if no error was found and false if an error was found.
 *
 * 1) All free blocks have neighboring allocated blocks.
 * 2) Allocated bit in block matches the previous allocation bit in next block.
 * 3) The segregated lists only contain free blocks.
 * 4) Block size in header matches block size in the footer.
 * 5) Amount of free blocks in the heap matches the amount of blocks contained
 *    in all of the segregated lists.
 * 
 *                Check heap error codes 
 *                NEIGHBOR_FREE_ERROR -1
 *                ALLOC_MISMATCH_ERROR -2
 *                ALLOC_IN_SLIST_ERROR -3
 *                HEADER_FOOTER_MISMATCH_ERROR -4
 *                SLIST_MISMATCH_ERROR -5
 *                BLOCK_SIZE_ALLOC_ERROR -6
 */
bool mm_checkheap(int line)
{
    /* Helper functions that return the amount of free blocks if return is
     * positive. If return is negative then an invariant was found and an
     * error is returned as one of the error codes defined above.
     */
    int free_blocks_in_heap = count_free_blocks_in_heap();
    int free_blocks_in_sList = count_free_blocks_in_sList();

    /* Free block has free neighboring block */
    if(free_blocks_in_heap == NEIGHBOR_FREE_ERROR) {
	dbg_printf("Free block has free neighbor \n");
	return false;
    }

    /* Make sure alloc and prev alloc bits are set correctly */
    if(free_blocks_in_heap == ALLOC_MISMATCH_ERROR) {
	dbg_printf("Prev alloc and alloc for prev block dont match \n");
	return false;
    }

    /* Make sure segregated list does not contain an allocated block */
    if(free_blocks_in_sList == ALLOC_IN_SLIST_ERROR) {
	printf("Allocated block in seg list \n");
        return false;
    }

    /* Make sure header size matches footer size */
    if(free_blocks_in_sList == HEADER_FOOTER_MISMATCH_ERROR) {
	dbg_printf("Header and footer dont match \n");
	return false;
    }

    /* Make sure all free blocks are in correct list */
    if(free_blocks_in_sList == SLIST_MISMATCH_ERROR) {
	dbg_printf("Block is in wrong seg list \n");
	return false;
    }

    /* Make sure 16 byte blocks have small block bit set
     * Make sure bigger blocks do not have small block bit set */
    if(free_blocks_in_heap == BLOCK_SIZE_ALLOC_ERROR) {
	dbg_printf("Small block bit not correctly set \n");
	return false;
    }

    /* Make sure free blocks in heap is the same as blocks in the sList */
    if(free_blocks_in_heap != free_blocks_in_sList) {
	dbg_printf("free blocks in heap do not match seg list \n");
	return false;
    }

    return true;
}

/*
 * max: returns x if x > y, and y otherwise.
 */
static size_t max(size_t x, size_t y)
{
    return (x > y) ? x : y;
}

/*
 * round_up: Rounds size up to next multiple of n
 */
static size_t round_up(size_t size, size_t n)
{
    return (n * ((size + (n-1)) / n));
}

/*
 * pack: returns a header reflecting a specified size, its alloc status, and.
 *       the previous block's alloc status. If the block is allocated, the
 *       lowest bit is set to 1, and 0 otherwise.
 */
static word_t pack(size_t size, bool alloc, bool prev_alloc)
{
    return size | alloc | (prev_alloc << PREV_ALLOC_SHIFT);
}


/*
 * extract_size: returns the size of a given header value based on the header
 *               specification above.
 */
static size_t extract_size(word_t word)
{
    return (word & size_mask);
}

/*
 * get_size: returns the size of a given block by clearing the lowest 4 bits
 *           (as the heap is 16-byte aligned).
 */
static size_t get_size(block_t *block)
{
    // return size 16 if small block
    if(get_16_alloc(block))
	return SIZE_1;
    return extract_size(block->header);
}

/*
 * get_payload_size: returns the payload size of a given block, equal to
 *                   the entire block size minus the header and footer sizes.
 */
static word_t get_payload_size(block_t *block)
{
    size_t asize = get_size(block);
    return asize - wsize;
}

/*
 * extract_alloc: returns the allocation status of a given header value based
 *                on the header specification above.
 */
static bool extract_alloc(word_t word)
{
    return (bool)(word & alloc_mask);
}

/*
 * extract_prev_alloc: returns the allocation status of a previous block based
 *                     on the header specification above.
 */
static bool extract_prev_alloc(word_t word)
{
    return (bool)((word >> PREV_ALLOC_SHIFT) & alloc_mask);
}

/*
 * get_alloc: returns true when the block is allocated based on the
 *            block header's lowest bit, and false otherwise.
 */
static bool get_alloc(block_t *block)
{
    return extract_alloc(block->header);
}

/*
 * get_prev_alloc: returns true when the previous block is allocated based
 *                 on the block header's second lowest bit, and false otherwise.
 */
static bool get_prev_alloc(block_t *block)
{
    return extract_prev_alloc(block->header);
}

/*
 * get_16_alloc: returns true when a block is of size 16 bytes and false
 *               otherwise. This is based off of the block header's 3rd least
 *               significant bit.
 */
static bool get_16_alloc(block_t * block) {
   return (bool)(block->header & SB_MASK);
}

/* pack_16: writes the header of a 16 byte block. If the block is free then
 *          the address of the next free block will be appended to the header.
 *          returns the new header as a word_t.
 */
static word_t pack_16(block_t *block, bool alloc, bool prev_alloc) {
  if(!alloc) {
    return (word_t) block | 
	   (1 << SMALL_BLOCK_SHIFT) | 
	   (prev_alloc << PREV_ALLOC_SHIFT) | 
	   alloc;
  }
  return (word_t) (1 << SMALL_BLOCK_SHIFT) | 
	 (prev_alloc << PREV_ALLOC_SHIFT) | 
	 alloc;
}

/* pack_16_f: Writes the footer of a 16 byte block. If the block is free then
 *            the address of the previous free block will be appended to the 
 *            footer. Returns the new footer as a word_t.
 */
static word_t pack_16_f(block_t *block, bool alloc) {
    if(!alloc) {
	return (word_t) block | (1 << SMALL_BLOCK_SHIFT) | alloc;
    }

   return (word_t) (1 << SMALL_BLOCK_SHIFT) | alloc;
}

/* 
 * write_header_16: Writes the header of a 16 byte block
 */
static void write_header_16(block_t *block, 
		            block_t *next_block, 
			    bool alloc, 
			    bool prev_alloc) {
    block->header = pack_16(next_block, alloc, prev_alloc);
}

/*
 * write_p_f: Writes the footer of a 16 byte block.
 */
static void write_p_f(block_t *block, block_t *prev_block, bool alloc) {
    block->p_f = pack_16(prev_block, alloc, 0);
}

/*
 * get_next_free: returns the next free block.
 */
static block_t *get_next_free(block_t *block) {
    if(get_size(block) == SIZE_1) {
	return (block_t *)((word_t) block->header & SB_HEADER_MASK);
    }
    return block->next;
}

/* 
 * get_prev_free: returns the previous free block.
 */
static block_t *get_prev_free(block_t *block) {
   if(get_size(block) == SIZE_1) {
	return (block_t *)((word_t) block->p_f & SB_HEADER_MASK);
   } else {
      return block->prev;
   }
}

/*
 * set_prev: sets the previous free block of a block.
 */
static void set_prev(block_t *block, block_t *block_prev) {
   if(get_size(block) == SIZE_1) {
      block->p_f = pack_16_f(block_prev, get_alloc(block));
   } else {
      block->prev = block_prev;
   }
}

/*
 * set_next: Sets the next free block of a block.
 */
static void set_next(block_t *block, block_t *block_next) {
   if(get_size(block) == SIZE_1) {
      block->header = pack_16(block_next, 
		              get_alloc(block), 
			      get_prev_alloc(block));
   } else {
      block->next = block_next;
   }
}

/*
 * write_header: given a block and its size and allocation status,
 *               writes an appropriate value to the block header.
 */
static void write_header(block_t *block, 
		         size_t size, 
			 bool alloc, 
			 bool prev_alloc) {
    if(size == SIZE_1) {
	block->header = pack_16(block, alloc, prev_alloc); 
	return;
    }
    block->header = pack(size, alloc, prev_alloc);
}


static bool get_16_alloc_h(word_t header) {
    return header & SB_MASK;
}


/*
 * write_footer: given a block and its size and allocation status,
 *               writes an appropriate value to the block footer by first
 *               computing the position of the footer.
 */
static void write_footer(block_t *block, size_t size, bool alloc)
{
    if(size == SIZE_1) {
	//block->p_f = pack_16_f(block, alloc);	
	return;
    }
    word_t *footerp = (word_t *)((block->payload) + get_size(block) - dsize);
    *footerp = pack(size, alloc, true);
}


/*
 * find_next: returns the next consecutive block on the heap by adding the
 *            size of the block.
 */
static block_t *find_next(block_t *block)
{
    dbg_requires(block != NULL);
    block_t *block_next = (block_t *)(((char *)block) + get_size(block));

    dbg_ensures(block_next != NULL);
    return block_next;
}

/*
 * find_prev_footer: returns the footer of the previous block.
 */
static word_t *find_prev_footer(block_t *block)
{
    // Compute previous footer position as one word before the header
    return (&(block->header)) - 1;
}

/*
 * find_prev: returns the previous block position by checking the previous
 *            block's footer and calculating the start of the previous block
 *            based on its size.
 */
static block_t *find_prev(block_t *block)
{
    word_t *footerp = find_prev_footer(block);
    size_t size = extract_size(*footerp);
    if(get_16_alloc_h(*footerp)) {
    	size = SIZE_1;
    }
    return (block_t *)((char *)block - size);
}

static bool is_free_alloc(block_t *block) {

    return false;
}

/*
 * payload_to_header: given a payload pointer, returns a pointer to the
 *                    corresponding block.
 */
static block_t *payload_to_header(void *bp)
{
    return (block_t *)(((char *)bp) - offsetof(block_t, payload));
}

/*
 * header_to_payload: given a block pointer, returns a pointer to the
 *                    corresponding payload.
 */
static void *header_to_payload(block_t *block)
{
    return (void *)(block->payload);
}

/*
 * size_to_sList: given a block size returns the corresponding
 *                list that would be associated with it.
 */
static int size_to_sList(size_t size) {
  if(size == SIZE_1) {
    return 0;
  } else if(size > SIZE_1 && size <= SIZE_2) {
    return 1;
  } else if(size > SIZE_2 && size <= SIZE_3) {
    return 2;
  } else if(size > SIZE_3 && size <= SIZE_4) {
    return 3;
  } else if(size > SIZE_4 && size <= SIZE_5) {
    return 4;
  } else if(size > SIZE_5 && size <= SIZE_6) {
    return 5;
  } else if(size > SIZE_6) {
    return 6;
  } else {
    return 0;
  }
}

/*
 * block_to_sList: given a block returns the corresponding
 *                list that would be associated with it.
 */

static int block_to_sList(block_t *block) {
   return size_to_sList(get_size(block)); 
}

/* 
 * print_block: Prints all of the contents of a block in a readable format.
 *              Each element is printed in its own print statement in case 
 *              of a segmentation fault so that it can be seen on which 
  *             element the segmentation fault occured.
 */
static void print_block(block_t *block) {
   dbg_printf("Block %p ", block);
   dbg_printf("Header %llx ", (long long) block->header);
   dbg_printf("Alloc %i ", get_alloc(block));
   if(!get_16_alloc(block)) {
        dbg_printf("Footer %ld ", (word_t) *find_prev_footer(find_next(block)));
        dbg_printf("Prev %p ", get_prev_free(block));
        dbg_printf("Next %p ", get_next_free(block));
   } else {
        dbg_printf("Prev %p ", (void *) (block->p_f & SB_HEADER_MASK));
	dbg_printf("Next %p ", (void *) (block->header & SB_HEADER_MASK));
	dbg_printf("P_F %llx ", (long long) block->p_f);
   }
   dbg_printf("Size %i ", (int) get_size(block));
   dbg_printf("Payload Size %i ", (int) get_payload_size(block));
   dbg_printf("Small Block %i ", (int) get_16_alloc(block));
   dbg_printf("Alloc %i ", get_alloc(block));
   dbg_printf("Prev Alloc %i \n", get_prev_alloc(block));
}

/*
 * print_free_blocks: Prints all of the blocks in the segregated lists.
 */
static void print_free_blocks() {
    dbg_printf("-------------Printing Free List--------------------------\n");
    block_t *block = freeList_start;

    printf("start -> %p\n", block);
    int count = 0;
    for(; count < SLIST_SIZE; count++) {
      printf("Printing list %i\n", count);
      block = sList[count];
      while(block) {
          print_block(block);
          block = get_next_free(block);
      }
    }
    dbg_printf(" END\n");
}

/*
 * print_heap: Prints out all of the blocks in the heap.
 */
static void print_heap() {
    dbg_printf("--------------Printing Heap--------------------\n");
    block_t *block;
    for (block = heap_start; get_size(block) > 0;
        block = find_next(block))
    {
        print_block(block);
    }
    dbg_printf(" END \n");
}


/*
 *  count_free_blocks_in_sList: Loops through all of the blocks in the  
 *                              segregated list and counts all of the blocks.
 *                              blocks. Returns an error code if an error
 *                              was found.
 */

static int count_free_blocks_in_sList() {
    block_t *block;
    int count = 0;
    int sListCounter = 0;
    for(; sListCounter < SLIST_SIZE; sListCounter++) {
        block = sList[sListCounter];
	for(; block != NULL; block = get_next_free(block)) {

	    /* Allocated block in the segregated list */
	    if(get_alloc(block)) {
	        return ALLOC_IN_SLIST_ERROR;
	    }

	    /* Make sure header size and footer size are equal */
	    if(!get_16_alloc(block) && ((int) extract_size(block->header) != 
	       (int) extract_size(*find_prev_footer(find_next(block))))) {
		print_block(block);
		return HEADER_FOOTER_MISMATCH_ERROR;
	    }

	    /* Make sure block should be in this list */
	    if(block_to_sList(block) != sListCounter) {
		return SLIST_MISMATCH_ERROR;
	    }

	    /* Increment free block counter */
	    count++;
	}
    }

    /* Returns the amount of blocks if no error found */
    return count;
}

/*
 *  count_free_blocks_in_heap: Loops through all of the blocks in the heap and 
 *                             counts all of the free blocks. Returns an error
 *                             code if an error is found. 
 */
static int count_free_blocks_in_heap() {
    block_t *block = heap_start;
    int count = 0;
    for(; get_size(block) > 0; block = find_next(block)) {
	if(!get_alloc(block)) {

	    /* Add block to counter if free */
 	    count++;

	    /* Block must not have free neighbors */
	    if(!get_prev_alloc(block) || !get_alloc(find_next(block))) {
	        return NEIGHBOR_FREE_ERROR;
	    }

	    /* Block alloc bit must match next block's prev alloc bit */
	    if( get_alloc(block) != get_prev_alloc(find_next(block))) {
         	return ALLOC_MISMATCH_ERROR;
	    }
	}

        /* Block alloc bit must match next block's prev alloc bit */
	if( get_alloc(block) != get_prev_alloc(find_next(block))) {
            return ALLOC_MISMATCH_ERROR;
	}

	/* 16 Byte block must have small block bit set.
	 * Bigger blocks must not have the small block bit set. */
	if(get_size(block) == SIZE_1 && !get_16_alloc(block)) {
	    return BLOCK_SIZE_ALLOC_ERROR;
	}

    }

    /* Returns the amount of free blocks if no error found */
    return count;
}

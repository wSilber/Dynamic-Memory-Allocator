/*
 ******************************************************************************
 *                               mm.c                                         *
 *           64-bit struct-based implicit free list memory allocator          *
 *                      without coalesce functionality                        *
 *                 CSE 361: Introduction to Computer Systems                  *
 *                                                                            *
 *  ************************************************************************  *
 *                     insert your documentation here. :)                     *
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
 #define DEBUG // uncomment this line to enable debugging

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
static const size_t min_block_size = 4*sizeof(word_t); // Minimum block size
static const size_t chunksize = (1 << 12);    // requires (chunksize % 16 == 0)

static const word_t alloc_mask = 0x1;
static const word_t size_mask = ~(word_t)0xF;

typedef struct block
{
    /* Header contains size + allocation flag */
    word_t header;
    /*
     * We don't know how big the payload will be.  Declaring it as an
     * array of size 0 allows computing its starting address using
     * pointer notation.
     */
    union {
        struct {
            struct block* prev;
            struct block* next;
        };
        char payload[0];
    };
    /*
     * We can't declare the footer as part of the struct, since its starting
     * position is unknown
     */
} block_t;


/* Global variables */
/* Pointer to first block */
static block_t *heap_start = NULL;

bool mm_checkheap(int lineno);

/* Function prototypes for internal helper routines */
static block_t *extend_heap(size_t size);
static void place(block_t *block, size_t asize);
static block_t *find_fit(size_t asize);
static block_t *coalesce(block_t *block);

static size_t max(size_t x, size_t y);
static size_t round_up(size_t size, size_t n);
static word_t pack(size_t size, bool alloc);

static size_t extract_size(word_t header);
static size_t get_size(block_t *block);
static size_t get_payload_size(block_t *block);

static bool extract_alloc(word_t header);
static bool get_alloc(block_t *block);

static void write_header(block_t *block, size_t size, bool alloc);
static void write_footer(block_t *block, size_t size, bool alloc);

static block_t *payload_to_header(void *bp);
static void *header_to_payload(block_t *block);

static block_t *find_next(block_t *block);
static word_t *find_prev_footer(block_t *block);
static block_t *find_prev(block_t *block);

/* Explicit List Functions And Variables */
static block_t *freeList_start = NULL;
static void add_free_block(block_t *block);
static void remove_free_block(block_t *block);
static void print_free_blocks();
static void print_block(block_t *block);
static void print_heap();

/*
 * <what does mm_init do?>
 */
bool mm_init(void) 
{
    // Create the initial empty heap 
    word_t *start = (word_t *)(mem_sbrk(2*wsize));

    if (start == (void *)-1) 
    {
        return false;
    }

    start[0] = pack(0, true); // Prologue footer
    start[1] = pack(0, true); // Epilogue header
    // Heap starts with first "block header", currently the epilogue footer
    heap_start = (block_t *) &(start[1]);

    freeList_start = heap_start;

    // Extend the empty heap with a free block of chunksize bytes
    if (extend_heap(chunksize) == NULL)
    {
        return false;
    }
    return true;
}

/*
 * <what does mmalloc do?>
 */
void *malloc(size_t size) 
{
    //print_heap();
   // print_free_blocks();
  //  printf("Malloc called for size %i\n", (int) size);
 //   print_free_blocks();
  //  printf("Malloc called\n");
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


    // Adjust block size to include overhead and to meet alignment requirements
    asize = round_up(size + dsize, dsize);

    // Search the free list for a fit
    block = find_fit(asize);
    

    // If no fit is found, request more memory, and then and place the block
    if (block == NULL)
    {  
        extendsize = max(asize, chunksize);
        block = extend_heap(extendsize);
        if (block == NULL) // extend_heap returns an error
        {
   //         printf("ERROR");
            return bp;
        }

    }
  //  printf("%p\n", block);
    place(block, asize);
    
    bp = header_to_payload(block);

    dbg_ensures(mm_checkheap(__LINE__));
    return bp;
} 

/*
 * <what does free do?>
 */
void free(void *bp)
{

    if (bp == NULL)
    {
        return;
    }

    block_t *block = payload_to_header(bp);
    size_t size = get_size(block);
 //   printf("Free called on block %p\n", block);

    write_header(block, size, false);
    write_footer(block, size, false);
   // printf("FREE CALLED\n");
    coalesce(block);
   /// printf("FREE FINISHED\n");

}

/*
 * <what does realloc do?>
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
 * <what does calloc do?>
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
 * <what does extend_heap do?>
 */
static block_t *extend_heap(size_t size) 
{
    //printf("Extending heap\n");
    void *bp;

    // Allocate an even number of words to maintain alignment
    size = round_up(size, dsize);
    if ((bp = mem_sbrk(size)) == (void *)-1)
    {
        return NULL;
    }
    
    // Initialize free block header/footer 
    block_t *block = payload_to_header(bp);
    write_header(block, size, false);
    write_footer(block, size, false);
    // Create new epilogue header
    block_t *block_next = find_next(block);
    write_header(block_next, 0, true);

    // Coalesce in case the previous block was free
    //printf("extending %p\n", coalesce(block));
    return coalesce(block);
}

/*
 * Adds a free block to the free block list
 */
static void add_free_block(block_t *block) {

    block->next = NULL;
    block->prev = NULL;
    if(!freeList_start) {
        freeList_start = block;
    }
    if(block != freeList_start) {
        block->next = freeList_start;
        freeList_start->prev = block;
        freeList_start = block;
    }
}

/*
 * Removes a free block from the free block list
 */
static void remove_free_block(block_t *block) {

    // Nothing in free list
    if(!freeList_start) {
        return;
    }

    // Block is the start of the free list
    if(!block->prev) {

        // Block is only block in free list
        if(!freeList_start->next) {
            freeList_start = NULL;

        // Block is not only block in free list
        } else {
            block->next->prev = NULL;
            freeList_start = block->next;
        }

    // Block is not the first block in the list
    } else {

        // Block is the last block in the free list
        if(!block->next) {
            block->prev->next = NULL;
            block->prev = NULL;

        // Block is in the middle of the list
        } else {
            block->prev->next = block->next;
            block->next->prev = block->prev;
        }
    }

    block->prev = NULL;
    block->next = NULL;

}

/*
 * <what does coalesce do?>
 */
static block_t *coalesce(block_t * block) 
{
    bool is_prev_block = get_alloc(find_prev(block)) || find_prev(block) == block;
    bool is_next_block = get_alloc(find_next(block));
    
    // Case 1: Surrounded by allocated blocks
    if(is_prev_block && is_next_block) {
       // printf("Case 1\n");
        size_t size = get_size(block);
        write_header(block, size, false);
        write_footer(block, size, false);

    // Case 2: Has allocated previous block
    } else if(is_prev_block && !is_next_block) {
      //  printf("Case 2\n");

        remove_free_block(find_next(block));
        //Size of new block equals size of block and next block
        size_t size = get_size(block) + get_size(find_next(block));

        write_header(block, size, false);
        write_footer(block, size, false);


    // // Case 3: Has allocated next block
    } else if(!is_prev_block && is_next_block) {
       // printf("Case 3\n");

        remove_free_block(find_prev(block));
        size_t size = get_size(block) + get_size(find_prev(block));

        block = find_prev(block);
        write_header(block, size, false);
        write_footer(block, size, false);
        
      //  printf("block %p\n", block);

    // Case 4: Surrounded by free blocks
    } else if(!is_prev_block && !is_next_block){
       // printf("Case 4\n");

        remove_free_block(find_prev(block));
        remove_free_block(find_next(block));
        size_t size = get_size(block) + get_size(find_prev(block)) + get_size(find_next(block));

       // printf("Finding size\n");
        block = find_prev(block);
        write_header(block, size, false);
        write_footer(block, size, false);

     }
    add_free_block(block);
    return block;
}

/*
 * <what does place do?>
 */
static void place(block_t *block, size_t asize)
{
    size_t csize = get_size(block);
    
    if ((csize - asize) >= min_block_size)
    {
        block_t *block_next;
        remove_free_block(block);
        write_header(block, asize, true);
        write_footer(block, asize, true);

        block_next = find_next(block);
        
        write_header(block_next, csize-asize, false);
        write_footer(block_next, csize-asize, false);
        add_free_block(block_next);
    }

    else
    { 
        write_header(block, csize, true);
        write_footer(block, csize, true);
        remove_free_block(block);
        
    }
    
}

/*
 * <what does find_fit do?>
 */
static block_t *find_fit(size_t asize)
{
   //printf("Attempting to find block of size %i\n", (int) asize);
  //  print_free_blocks();
    block_t *block;
    size_t smallest_size = 0x7fffffff;
    int n = 1;
    block_t *best_block = NULL;
    size_t block_size = 0;

    for (block = freeList_start; block->next != NULL && n > 0; block = block->next) {

        block_size = get_size(block);
        if (!(get_alloc(block)) && (asize <= block_size))
        {

            if(block_size == asize) {
            //    printf("Found block of perfect size\n");
            //    print_block(block);
                return block;
            }
            if(block_size < smallest_size) {
            //    printf("Found smaller block %i\n", (int) block_size);
            //    print_block(block);
                n--;
                best_block = block;
                smallest_size = get_size(block);
              //  printf("%i\n", n);
            }
        }
    }
//     if(n == 0) {
//         printf("N = 0\n");
//     }
//    if(!block->next)
//        printf("Reached the end of the freelist\n");
//    printf("Using block of size %i\n", (int)  block_size);
//    if(best_block)
//     print_block(best_block);
   return best_block; // no fit found
}

/* 
 * <what does your heap checker do?>
 * Please keep modularity in mind when you're writing the heap checker!
 */
bool mm_checkheap(int line)  
{ 
    (void)line; // delete this line; it's a placeholder so that the compiler
                // will not warn you about an unused variable.

    //Check to make sure there are no free blocks next to each other -> Coalessing

    //Check to make sure there is a pointer to a doubly linked list for every free block

    //Make sure every free block is actually free -> Count amount of free blocks

    // Have 4 extra bits at beginning of header
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
 * pack: returns a header reflecting a specified size and its alloc status.
 *       If the block is allocated, the lowest bit is set to 1, and 0 otherwise.
 */
static word_t pack(size_t size, bool alloc)
{
    return alloc ? (size | alloc_mask) : size;
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
    return extract_size(block->header);
}

/*
 * get_payload_size: returns the payload size of a given block, equal to
 *                   the entire block size minus the header and footer sizes.
 */
static word_t get_payload_size(block_t *block)
{
    size_t asize = get_size(block);
    return asize - dsize;
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
 * get_alloc: returns true when the block is allocated based on the
 *            block header's lowest bit, and false otherwise.
 */
static bool get_alloc(block_t *block)
{
    return extract_alloc(block->header);
}

/*
 * write_header: given a block and its size and allocation status,
 *               writes an appropriate value to the block header.
 */
static void write_header(block_t *block, size_t size, bool alloc)
{
    block->header = pack(size, alloc);
}


/*
 * write_footer: given a block and its size and allocation status,
 *               writes an appropriate value to the block footer by first
 *               computing the position of the footer.
 */
static void write_footer(block_t *block, size_t size, bool alloc)
{
    word_t *footerp = (word_t *)((block->payload) + get_size(block) - dsize);
    *footerp = pack(size, alloc);
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
    return (block_t *)((char *)block - size);
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

static void print_block(block_t *block) {
    dbg_printf("Block %p Prev %p Next %p Size %i Allocated %i\n", block, block->prev, block->next, (int) get_size(block), get_alloc(block));
}

static void print_free_blocks() {
    dbg_printf("-------------Printing Free List----------------------------\n");
    block_t *block = freeList_start;

    printf("start -> %p\n", block);
    while(block) {
        print_block(block);
        //printf("%p ", block);
        block = block->next;
    }
    printf(" END\n");
}

static void print_heap() {
    dbg_printf("-----------------------------------------\n");
    block_t *block;
    for (block = heap_start; get_size(block) > 0;
        block = find_next(block))
    {
        print_block(block);

    }
}
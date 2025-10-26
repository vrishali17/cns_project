#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAX_DIGITS 200
#define BASE 10000
#define MAX_BLOCK_SIZE 32
#define MILLER_RABIN_ROUNDS 5

// BigInt structure
typedef struct {
    int digits[MAX_DIGITS];
    int length;
    int sign;
} BigInt;

// Performance metrics
typedef struct {
    double key_gen_time;
    double encryption_time;
    double decryption_time;
    int blocks_processed;
} PerformanceMetrics;

// RSA Key
typedef struct {
    BigInt n;
    BigInt e;
    int bits;
} RSAKey;

// Encrypted block
typedef struct {
    BigInt value;
    int original_length;
} EncryptedBlock;

// ============= BIGINT OPERATIONS =============

void bigint_init(BigInt *num) {
    memset(num->digits, 0, sizeof(num->digits));
    num->length = 1;
    num->sign = 1;
}

void bigint_from_int(BigInt *num, long long val) {
    bigint_init(num);
    if (val < 0) {
        num->sign = -1;
        val = -val;
    }
    int i = 0;
    while (val > 0) {
        num->digits[i++] = val % BASE;
        val /= BASE;
    }
    num->length = (i > 0) ? i : 1;
}

void bigint_copy(BigInt *dest, const BigInt *src) {
    memcpy(dest->digits, src->digits, sizeof(int) * src->length);
    dest->length = src->length;
    dest->sign = src->sign;
}

void bigint_print(const BigInt *num) {
    if (num->sign < 0) printf("-");
    printf("%d", num->digits[num->length - 1]);
    for (int i = num->length - 2; i >= 0; i--) {
        printf("%04d", num->digits[i]);
    }
}

int bigint_compare(const BigInt *a, const BigInt *b) {
    if (a->sign != b->sign) return a->sign;
    if (a->length != b->length) 
        return a->sign * ((a->length > b->length) ? 1 : -1);
    
    for (int i = a->length - 1; i >= 0; i--) {
        if (a->digits[i] != b->digits[i])
            return a->sign * ((a->digits[i] > b->digits[i]) ? 1 : -1);
    }
    return 0;
}

int bigint_is_zero(const BigInt *num) {
    return num->length == 1 && num->digits[0] == 0;
}

int bigint_is_even(const BigInt *num) {
    return (num->digits[0] & 1) == 0;
}

void bigint_add(BigInt *result, const BigInt *a, const BigInt *b) {
    int carry = 0;
    int max_len = (a->length > b->length) ? a->length : b->length;
    
    for (int i = 0; i < max_len || carry; i++) {
        int sum = carry;
        if (i < a->length) sum += a->digits[i];
        if (i < b->length) sum += b->digits[i];
        
        result->digits[i] = sum % BASE;
        carry = sum / BASE;
    }
    
    result->length = max_len;
    if (carry) result->digits[result->length++] = carry;
    while (result->length > 1 && result->digits[result->length - 1] == 0)
        result->length--;
    result->sign = 1;
}

void bigint_subtract(BigInt *result, const BigInt *a, const BigInt *b) {
    int borrow = 0;
    
    for (int i = 0; i < a->length; i++) {
        int diff = a->digits[i] - borrow;
        if (i < b->length) diff -= b->digits[i];
        
        if (diff < 0) {
            diff += BASE;
            borrow = 1;
        } else {
            borrow = 0;
        }
        result->digits[i] = diff;
    }
    
    result->length = a->length;
    while (result->length > 1 && result->digits[result->length - 1] == 0)
        result->length--;
    result->sign = 1;
}

// Simple multiplication (will be optimized with Karatsuba)
void bigint_multiply_simple(BigInt *result, const BigInt *a, const BigInt *b) {
    memset(result->digits, 0, sizeof(result->digits));
    
    for (int i = 0; i < a->length; i++) {
        long long carry = 0;
        for (int j = 0; j < b->length || carry; j++) {
            long long prod = result->digits[i + j] + carry;
            if (j < b->length)
                prod += (long long)a->digits[i] * b->digits[j];
            
            result->digits[i + j] = prod % BASE;
            carry = prod / BASE;
        }
    }
    
    result->length = a->length + b->length;
    while (result->length > 1 && result->digits[result->length - 1] == 0)
        result->length--;
    result->sign = a->sign * b->sign;
}

// Karatsuba multiplication (Schönhage-Strassen inspired)
void bigint_karatsuba(BigInt *result, const BigInt *x, const BigInt *y) {
    // Base case: use simple multiplication for small numbers
    if (x->length <= 4 || y->length <= 4) {
        bigint_multiply_simple(result, x, y);
        return;
    }
    
    int m = (x->length > y->length ? x->length : y->length) / 2;
    
    BigInt x_low, x_high, y_low, y_high;
    bigint_init(&x_low); bigint_init(&x_high);
    bigint_init(&y_low); bigint_init(&y_high);
    
    // Split numbers: x = x_high * BASE^m + x_low
    for (int i = 0; i < m && i < x->length; i++) 
        x_low.digits[i] = x->digits[i];
    x_low.length = (m < x->length) ? m : x->length;
    
    for (int i = m; i < x->length; i++) 
        x_high.digits[i - m] = x->digits[i];
    x_high.length = (x->length > m) ? x->length - m : 1;
    
    for (int i = 0; i < m && i < y->length; i++) 
        y_low.digits[i] = y->digits[i];
    y_low.length = (m < y->length) ? m : y->length;
    
    for (int i = m; i < y->length; i++) 
        y_high.digits[i - m] = y->digits[i];
    y_high.length = (y->length > m) ? y->length - m : 1;
    
    // Three recursive multiplications
    BigInt z0, z1, z2, temp1, temp2;
    bigint_init(&z0); bigint_init(&z1); bigint_init(&z2);
    bigint_init(&temp1); bigint_init(&temp2);
    
    bigint_karatsuba(&z0, &x_low, &y_low);      // z0 = x_low * y_low
    bigint_karatsuba(&z2, &x_high, &y_high);    // z2 = x_high * y_high
    
    bigint_add(&temp1, &x_low, &x_high);
    bigint_add(&temp2, &y_low, &y_high);
    bigint_karatsuba(&z1, &temp1, &temp2);      // z1 = (x_low+x_high)*(y_low+y_high)
    bigint_subtract(&z1, &z1, &z0);
    bigint_subtract(&z1, &z1, &z2);
    
    // Combine: result = z2*BASE^(2m) + z1*BASE^m + z0
    memset(result->digits, 0, sizeof(result->digits));
    for (int i = 0; i < z0.length; i++) 
        result->digits[i] += z0.digits[i];
    for (int i = 0; i < z1.length; i++) 
        result->digits[i + m] += z1.digits[i];
    for (int i = 0; i < z2.length; i++) 
        result->digits[i + 2*m] += z2.digits[i];
    
    // Handle carries
    int carry = 0;
    result->length = x->length + y->length;
    for (int i = 0; i < result->length; i++) {
        result->digits[i] += carry;
        carry = result->digits[i] / BASE;
        result->digits[i] %= BASE;
    }
    
    while (result->length > 1 && result->digits[result->length - 1] == 0)
        result->length--;
    result->sign = x->sign * y->sign;
}

void bigint_divide_by_2(BigInt *num) {
    int carry = 0;
    for (int i = num->length - 1; i >= 0; i--) {
        int current = num->digits[i] + carry * BASE;
        num->digits[i] = current / 2;
        carry = current % 2;
    }
    while (num->length > 1 && num->digits[num->length - 1] == 0)
        num->length--;
}

void bigint_divide(BigInt *quotient, BigInt *remainder, const BigInt *dividend, const BigInt *divisor) {
    bigint_init(quotient);
    bigint_copy(remainder, dividend);
    
    if (bigint_compare(dividend, divisor) < 0) return;
    
    BigInt current, temp, two;
    bigint_from_int(&current, 1);
    bigint_from_int(&two, 2);
    bigint_copy(&temp, divisor);
    
    // Scale divisor up
    while (bigint_compare(&temp, dividend) <= 0) {
        bigint_add(&temp, &temp, &temp);
        bigint_add(&current, &current, &current);
    }
    
    // Divide back down
    while (!bigint_is_zero(&current)) {
        if (bigint_compare(remainder, &temp) >= 0) {
            bigint_subtract(remainder, remainder, &temp);
            bigint_add(quotient, quotient, &current);
        }
        bigint_divide_by_2(&current);
        bigint_divide_by_2(&temp);
    }
}

void bigint_mod(BigInt *result, const BigInt *a, const BigInt *m) {
    BigInt quotient;
    bigint_init(&quotient);
    bigint_divide(&quotient, result, a, m);
}

// Schönhage modular exponentiation using Karatsuba
void schonhage_mod_exp(BigInt *result, const BigInt *base, const BigInt *exponent, const BigInt *modulus) {
    BigInt temp_base, temp_exp, temp;
    bigint_copy(&temp_base, base);
    bigint_copy(&temp_exp, exponent);
    bigint_from_int(result, 1);
    
    bigint_mod(&temp_base, &temp_base, modulus);
    
    while (!bigint_is_zero(&temp_exp)) {
        if (!bigint_is_even(&temp_exp)) {
            bigint_karatsuba(&temp, result, &temp_base);
            bigint_mod(result, &temp, modulus);
        }
        
        bigint_karatsuba(&temp, &temp_base, &temp_base);
        bigint_mod(&temp_base, &temp, modulus);
        
        bigint_divide_by_2(&temp_exp);
    }
}

// ============= RSA FUNCTIONS =============

int miller_rabin_test(const BigInt *n, int rounds) {
    if (bigint_is_even(n)) return 0;
    
    BigInt n_minus_1, d, a, x, one, temp;
    bigint_copy(&n_minus_1, n);
    n_minus_1.digits[0]--;
    
    bigint_copy(&d, &n_minus_1);
    int r = 0;
    while (bigint_is_even(&d)) {
        bigint_divide_by_2(&d);
        r++;
    }
    
    bigint_from_int(&one, 1);
    
    for (int i = 0; i < rounds; i++) {
        bigint_from_int(&a, 2 + rand() % 1000);
        
        schonhage_mod_exp(&x, &a, &d, n);
        
        if (bigint_compare(&x, &one) == 0 || bigint_compare(&x, &n_minus_1) == 0)
            continue;
        
        int composite = 1;
        for (int j = 0; j < r - 1; j++) {
            bigint_karatsuba(&temp, &x, &x);
            bigint_mod(&x, &temp, n);
            
            if (bigint_compare(&x, &n_minus_1) == 0) {
                composite = 0;
                break;
            }
        }
        
        if (composite) return 0;
    }
    
    return 1;
}

void generate_prime(BigInt *result, int bits) {
    int attempts = 0;
    printf("Generating %d-bit prime...\n", bits);
    
    while (1) {
        bigint_init(result);
        
        // Generate random odd number
        int num_digits = bits / 14 + 1;  // BASE = 10000 ≈ 2^14
        for (int i = 0; i < num_digits; i++) {
            result->digits[i] = rand() % BASE;
        }
        result->length = num_digits;
        result->digits[0] |= 1; // Make odd
        result->digits[num_digits - 1] = rand() % (BASE/2) + BASE/2; // Ensure high bit
        
        if (miller_rabin_test(result, MILLER_RABIN_ROUNDS)) {
            printf("Prime found after %d attempts!\n", attempts + 1);
            return;
        }
        attempts++;
        if (attempts % 10 == 0) printf("Attempt %d...\n", attempts);
    }
}

void extended_gcd(BigInt *gcd, BigInt *x, BigInt *y, const BigInt *a, const BigInt *b) {
    if (bigint_is_zero(b)) {
        bigint_copy(gcd, a);
        bigint_from_int(x, 1);
        bigint_from_int(y, 0);
        return;
    }
    
    BigInt quotient, remainder, x1, y1, temp;
    bigint_divide(&quotient, &remainder, a, b);
    
    extended_gcd(gcd, &x1, &y1, b, &remainder);
    
    bigint_copy(x, &y1);
    bigint_karatsuba(&temp, &quotient, &y1);
    bigint_subtract(y, &x1, &temp);
}

void generate_rsa_keypair(RSAKey *public_key, RSAKey *private_key, int bits) {
    printf("\n=== Generating %d-bit RSA Key Pair ===\n", bits);
    
    BigInt p, q, phi, p_minus_1, q_minus_1, gcd, x, y;
    
    generate_prime(&p, bits / 2);
    generate_prime(&q, bits / 2);
    
    // n = p * q (using Karatsuba)
    printf("Computing modulus n = p * q...\n");
    bigint_karatsuba(&public_key->n, &p, &q);
    bigint_copy(&private_key->n, &public_key->n);
    
    // phi = (p-1)(q-1)
    printf("Computing phi(n)...\n");
    bigint_copy(&p_minus_1, &p);
    p_minus_1.digits[0]--;
    bigint_copy(&q_minus_1, &q);
    q_minus_1.digits[0]--;
    bigint_karatsuba(&phi, &p_minus_1, &q_minus_1);
    
    // e = 65537
    bigint_from_int(&public_key->e, 65537);
    
    // d = e^-1 mod phi
    printf("Computing private exponent d...\n");
    extended_gcd(&gcd, &x, &y, &public_key->e, &phi);
    
    if (x.sign < 0) {
        bigint_add(&private_key->e, &x, &phi);
    } else {
        bigint_copy(&private_key->e, &x);
    }
    
    public_key->bits = bits;
    private_key->bits = bits;
    
    printf("✓ RSA keys generated successfully!\n\n");
}

void encrypt_block(EncryptedBlock *encrypted, const unsigned char *data, int length, RSAKey *public_key) {
    BigInt plaintext;
    bigint_init(&plaintext);
    
    // Convert bytes to BigInt
    for (int i = 0; i < length; i++) {
        int digit_index = i / 2;
        int byte_pos = i % 2;
        plaintext.digits[digit_index] |= ((int)data[i]) << (byte_pos * 8);
    }
    plaintext.length = (length + 1) / 2;
    
    // Encrypt using Schönhage modular exponentiation
    schonhage_mod_exp(&encrypted->value, &plaintext, &public_key->e, &public_key->n);
    encrypted->original_length = length;
}

void decrypt_block(unsigned char *data, EncryptedBlock *encrypted, RSAKey *private_key) {
    BigInt plaintext;
    
    // Decrypt using Schönhage modular exponentiation
    schonhage_mod_exp(&plaintext, &encrypted->value, &private_key->e, &private_key->n);
    
    // Convert BigInt back to bytes
    for (int i = 0; i < encrypted->original_length; i++) {
        int digit_index = i / 2;
        int byte_pos = i % 2;
        data[i] = (plaintext.digits[digit_index] >> (byte_pos * 8)) & 0xFF;
    }
}

int main() {
    srand(time(NULL));
    
    printf("╔═══════════════════════════════════════════════════════════╗\n");
    printf("║  RSA Image Encryption - Schönhage-Strassen Technique      ║\n");
    printf("╚═══════════════════════════════════════════════════════════╝\n\n");
    
    RSAKey public_key, private_key;
    PerformanceMetrics metrics = {0};
    
    // Generate keys
    clock_t start = clock();
    generate_rsa_keypair(&public_key, &private_key, 128);  // Small for demo
    metrics.key_gen_time = (double)(clock() - start) / CLOCKS_PER_SEC * 1000;
    
    // Test data (simulating image pixels)
    unsigned char test_data[] = {255, 200, 150, 100, 50, 25, 10, 5};
    int data_len = sizeof(test_data);
    
    printf("Original data:  ");
    for (int i = 0; i < data_len; i++) printf("%3d ", test_data[i]);
    printf("\n");
    
    // Encrypt
    EncryptedBlock encrypted;
    start = clock();
    encrypt_block(&encrypted, test_data, data_len, &public_key);
    metrics.encryption_time = (double)(clock() - start) / CLOCKS_PER_SEC * 1000;
    
    printf("Encrypted:      ");
    bigint_print(&encrypted.value);
    printf("\n");
    
    // Decrypt
    unsigned char decrypted[MAX_BLOCK_SIZE];
    start = clock();
    decrypt_block(decrypted, &encrypted, &private_key);
    metrics.decryption_time = (double)(clock() - start) / CLOCKS_PER_SEC * 1000;
    
    printf("Decrypted data: ");
    for (int i = 0; i < data_len; i++) printf("%3d ", decrypted[i]);
    printf("\n\n");
    
    // Verify
    int match = 1;
    for (int i = 0; i < data_len; i++) {
        if (test_data[i] != decrypted[i]) {
            match = 0;
            break;
        }
    }
    
    printf("Verification: %s\n\n", match ? "✓ SUCCESS" : "✗ FAILED");
    
    // Performance metrics
    printf("╔═══════════════════════════════════════════════════════════╗\n");
    printf("║           Performance Metrics (Karatsuba Method)          ║\n");
    printf("╠═══════════════════════════════════════════════════════════╣\n");
    printf("║  Key Generation: %8.2f ms                                 ║\n", metrics.key_gen_time);
    printf("║  Encryption:     %8.2f ms                                 ║\n", metrics.encryption_time);
    printf("║  Decryption:     %8.2f ms                                 ║\n", metrics.decryption_time);
    printf("║  Data Size:      %8d bytes                                ║\n", data_len);
    printf("╚═══════════════════════════════════════════════════════════╝\n");
    
    return 0;
}
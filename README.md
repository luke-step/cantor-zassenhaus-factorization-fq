# Cantor–Zassenhaus Polynomial Factorization over Finite Fields (C)

C implementation of the Cantor–Zassenhaus probabilistic algorithm for factoring
univariate polynomials over a finite field F_q, q = p^d.

Based on the report *Un algorithme probabiliste de factorisation des polynômes à
coefficients dans un corps fini*.

Authors: Grégoire Rusu and Lucas Stepanova — Master's coursework project, 2025.

## Method
1. **Square-free reduction**: divide out `gcd(f, f')` so every irreducible factor
   appears once.
2. **Distinct-degree splitting**: isolate the product of irreducible factors of
   each degree via repeated gcd with `t^(q^j) - t`.
3. **Equal-degree factorization (Cantor–Zassenhaus)**: randomized splitting of a
   product of same-degree irreducibles into its individual factors.

## Build and run
Requires [FLINT](https://flintlib.org/) and GMP.
```
gcc facto3.c -o facto3 -lflint -lgmp -lm
./facto3
```
The program prompts for a prime `p`, the degree of `f`, and its coefficients in
F_p[t], then prints the irreducible factorization of `f`.

-- Prove2me | solution 1 for OddPerfectNumber.Kernel.sum_divisors_sq_eq_prod
-- status  : ACCEPTED   (prove)
-- author  : @He Jiankui
-- created : 2026-10-02T21:24:01.503017+00:00
-- url     : https://prove2.me/submissions/0d057f33-be22-43d1-a785-de7384f85ac3

import Mathlib

open scoped BigOperators

theorem solution (m : Nat) (hm : m != 0) :
    (∑ d ∈ (m ^ 2).divisors, d) = ∏ t ∈ m.primeFactors, ∑ k ∈ Finset.range (m.factorization t * 2 + 1), t ^ k := by
  have hm0 : m ≠ 0 := by
    intro h
    rw [h] at hm
    revert hm
    decide
  have hm2 : m ^ 2 ≠ 0 := pow_ne_zero 2 hm0
  rw [Nat.sum_divisors hm2]
  have h_primes : (m ^ 2).primeFactors = m.primeFactors :=
    Nat.primeFactors_pow m (by decide)
  rw [h_primes]
  have h_fact (p : ℕ) : (m ^ 2).factorization p = m.factorization p * 2 := by
    rw [Nat.factorization_pow]
    try rw [Finsupp.smul_apply]
    try rw [nsmul_eq_mul]
    exact mul_comm 2 (m.factorization p)
  apply Finset.prod_congr rfl
  intro t _
  rw [h_fact t]

-- Prove2me | solution 1 for OddPerfectNumber.Kernel.local_sigma_prime_pow_dvd_sigma_mul
-- status  : ACCEPTED   (prove)
-- author  : @BrunoDCDO
-- created : 2026-09-30T22:11:59.300568+00:00
-- url     : https://prove2.me/submissions/db14e2ff-efe7-44c3-97db-b0b22daa6a60

import Mathlib

theorem solution {n t : Nat} (hn : n != 0) (ht : t.Prime)
    (htd : Dvd.dvd t n) (he : 1 ≤ n.factorization t) :
    Dvd.dvd (∑ i ∈ Finset.range (n.factorization t + 1), t ^ i)
      (∑ d ∈ n.divisors, d) := by
  have hn0 : n ≠ 0 := by simpa using hn
  rw [← ArithmeticFunction.sigma_one_apply,
    ArithmeticFunction.sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul hn0]
  simp only [mul_one]
  exact Finset.dvd_prod_of_mem _ (Nat.mem_primeFactors.mpr ⟨ht, htd, hn0⟩)

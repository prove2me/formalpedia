-- Prove2me | solution 1 for OddPerfectNumber.Kernel.local_sigma_odd_prime_pow_dvd
-- status  : ACCEPTED   (prove)
-- author  : @BrunoDCDO
-- created : 2026-09-30T22:19:21.335036+00:00
-- url     : https://prove2.me/submissions/cd088f51-2bf1-4a77-8c3f-196ae32bed88

import Mathlib

theorem solution {m t : Nat} (ht : t.Prime) (htd : Dvd.dvd t (m ^ 2))
    (he : 1 ≤ (m ^ 2).factorization t) :
    Dvd.dvd (∑ i ∈ Finset.range ((m ^ 2).factorization t + 1), t ^ i)
      (∑ d ∈ (m ^ 2).divisors, d) := by
  have hm : m ≠ 0 := by
    intro hm
    simp [hm] at he
  have hn : m ^ 2 ≠ 0 := pow_ne_zero 2 hm
  rw [← ArithmeticFunction.sigma_one_apply,
    ArithmeticFunction.sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul hn]
  simp only [mul_one]
  exact Finset.dvd_prod_of_mem _ (Nat.mem_primeFactors.mpr ⟨ht, htd, hn⟩)

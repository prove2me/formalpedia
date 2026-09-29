-- Prove2me | solution 1 for OddPerfectNumber.sigma_eq_local_prod
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-11T09:54:03.48538+00:00
-- url     : https://prove2.me/submissions/0c307fad-b6e6-4a42-a8a7-8a14c5485bdc

import Mathlib

-- STAGED direct proof: the divisor-sum/product bridge used across the whole
-- valuation-flow thread (exists_source era), republished standalone.
-- Names verified repeatedly against pinned Mathlib.
theorem solution (m : Nat) (hm : m ^ 2 ≠ 0) :
    (∑ x ∈ (m ^ 2).divisors, x)
      = ∏ q ∈ (m ^ 2).primeFactors,
        ∑ i ∈ Finset.range ((m ^ 2).factorization q + 1), q ^ i := by
  have hsum : (∑ x ∈ (m ^ 2).divisors, x)
      = ArithmeticFunction.sigma 1 (m ^ 2) :=
    (ArithmeticFunction.sigma_one_apply (m ^ 2)).symm
  have hprod : ArithmeticFunction.sigma 1 (m ^ 2)
      = ∏ q ∈ (m ^ 2).primeFactors,
        ∑ i ∈ Finset.range ((m ^ 2).factorization q + 1), q ^ i := by
    simpa only [mul_one] using
      ArithmeticFunction.sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul
        (k := 1) (n := m ^ 2) hm
  exact hsum.trans hprod

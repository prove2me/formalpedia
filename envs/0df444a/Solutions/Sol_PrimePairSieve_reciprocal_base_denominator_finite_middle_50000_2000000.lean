-- Prove2me | solution 1 for PrimePairSieve.reciprocal_base_denominator_finite_middle_50000_2000000
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T23:03:07.610685+00:00
-- url     : https://prove2.me/submissions/2ad4f4f5-8095-4879-a458-9f91e976329c

import Theorems.Thm_PrimePairSieve_reciprocal_mass_window_50000_1300000
import Theorems.Thm_PrimePairSieve_reciprocal_threshold_tail_1300000
open scoped BigOperators
set_option autoImplicit false

theorem solution :
    ∀ z : ℝ, 50000 ≤ z → z ≤ 2000000 →
      (Real.log (4 * z)) ^ 2 / (2 * TaoFivePrimes.twinPrimeConstant) /
          (1 - ((z + 1) * ((Real.log (4 * z)) ^ 2 /
            (2 * TaoFivePrimes.twinPrimeConstant)) / (16 * z ^ 2)))
        ≤ ∑ q ∈ Finset.Icc 1 ⌊z⌋₊,
          (if Squarefree q then
            ∏ p ∈ q.primeFactors, if p = 2 then (1 : ℝ) else 2 / ((p : ℝ) - 2)
          else 0) / (1 + (q : ℝ) / z)  := by
  intro z hz hu
  by_cases h : z ≤ 1300000
  · exact PrimePairSieve.reciprocal_mass_window_50000_1300000 z hz h
  exact PrimePairSieve.reciprocal_threshold_tail_1300000 z (le_of_lt (lt_of_not_ge h))
#print axioms solution

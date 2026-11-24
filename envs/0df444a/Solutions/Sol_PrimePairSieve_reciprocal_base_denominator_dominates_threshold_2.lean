-- Prove2me | solution 2 for PrimePairSieve.reciprocal_base_denominator_dominates_threshold
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T19:32:51.165034+00:00
-- url     : https://prove2.me/submissions/cc99128c-45a5-41b4-a58a-fb921fada29d

import Theorems.Thm_PrimePairSieve_reciprocal_base_denominator_finite_500
import Theorems.Thm_PrimePairSieve_reciprocal_batched_window_500_5000
import Theorems.Thm_PrimePairSieve_reciprocal_base_denominator_finite_middle_5000_2000000
import Theorems.Thm_PrimePairSieve_reciprocal_base_denominator_dominates_threshold_large
set_option autoImplicit false
open scoped BigOperators

theorem solution :
∀ z : ℝ, 40 ≤ z →
      (Real.log (4 * z)) ^ 2 / (2 * TaoFivePrimes.twinPrimeConstant) /
          (1 - ((z + 1) * ((Real.log (4 * z)) ^ 2 /
            (2 * TaoFivePrimes.twinPrimeConstant)) / (16 * z ^ 2)))
        ≤ ∑ q ∈ Finset.Icc 1 ⌊z⌋₊,
          (if Squarefree q then
            ∏ p ∈ q.primeFactors, if p = 2 then (1 : ℝ) else 2 / ((p : ℝ) - 2)
          else 0) / (1 + (q : ℝ) / z) := by
  intro z hz
  by_cases h500 : z ≤ 500
  · exact PrimePairSieve.reciprocal_base_denominator_finite_500 z hz h500
  by_cases h5000 : z ≤ 5000
  · exact PrimePairSieve.reciprocal_batched_window_500_5000 z (le_of_lt (lt_of_not_ge h500)) h5000
  by_cases htail : z ≤ 2000000
  · exact PrimePairSieve.reciprocal_base_denominator_finite_middle_5000_2000000 z (le_of_lt (lt_of_not_ge h5000)) htail
  exact PrimePairSieve.reciprocal_base_denominator_dominates_threshold_large z (le_of_lt (lt_of_not_ge htail))

example : ∀ z : ℝ, 40 ≤ z →
      (Real.log (4 * z)) ^ 2 / (2 * TaoFivePrimes.twinPrimeConstant) /
          (1 - ((z + 1) * ((Real.log (4 * z)) ^ 2 /
            (2 * TaoFivePrimes.twinPrimeConstant)) / (16 * z ^ 2)))
        ≤ ∑ q ∈ Finset.Icc 1 ⌊z⌋₊,
          (if Squarefree q then
            ∏ p ∈ q.primeFactors, if p = 2 then (1 : ℝ) else 2 / ((p : ℝ) - 2)
          else 0) / (1 + (q : ℝ) / z) := solution
#print axioms solution

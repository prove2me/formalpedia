-- Prove2me | solution 1 for PrimePairSieve.reciprocal_base_denominator_finite_middle_5000_2000000
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T21:21:56.012849+00:00
-- url     : https://prove2.me/submissions/d193f9cc-7595-4c6a-958f-a1f4901c0226

import Theorems.Thm_PrimePairSieve_reciprocal_batched_window_5000_20000
import Theorems.Thm_PrimePairSieve_reciprocal_mass_window_20000_50000
import Theorems.Thm_PrimePairSieve_reciprocal_base_denominator_finite_middle_50000_2000000
open scoped BigOperators
set_option autoImplicit false

theorem solution : ∀ z : ℝ, 5000 ≤ z → z ≤ 2000000 →
      (Real.log (4 * z)) ^ 2 / (2 * TaoFivePrimes.twinPrimeConstant) /
          (1 - ((z + 1) * ((Real.log (4 * z)) ^ 2 /
            (2 * TaoFivePrimes.twinPrimeConstant)) / (16 * z ^ 2)))
        ≤ ∑ q ∈ Finset.Icc 1 ⌊z⌋₊,
          (if Squarefree q then
            ∏ p ∈ q.primeFactors, if p = 2 then (1 : ℝ) else 2 / ((p : ℝ) - 2)
          else 0) / (1 + (q : ℝ) / z) := by
  intro z hz hu
  by_cases h20 : z ≤ 20000
  · exact PrimePairSieve.reciprocal_batched_window_5000_20000 z hz h20
  by_cases h50 : z ≤ 50000
  · exact PrimePairSieve.reciprocal_mass_window_20000_50000 z (le_of_lt (lt_of_not_ge h20)) h50
  exact PrimePairSieve.reciprocal_base_denominator_finite_middle_50000_2000000
    z (le_of_lt (lt_of_not_ge h50)) hu
#print axioms solution

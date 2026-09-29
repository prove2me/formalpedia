-- Prove2me | solution 1 for TaoFivePrimes.mawia_reciprocal_sum_bound_large
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-25T13:56:46.690811+00:00
-- url     : https://prove2.me/submissions/c454c4d9-b5b2-48f6-9fb8-840bfa739f2f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_TaoFivePrimes_mawia_reciprocal_sum_upper_bound_large
import Theorems.Thm_TaoFivePrimes_mawia_reciprocal_sum_lower_bound_large
import Mathlib

open TaoFivePrimes

theorem solution (x : ℝ) (hlarge : 10 ^ 8 ≤ x) :
    |(∑ p ∈ Nat.primesLE ⌊x⌋₊, 1 / (p : ℝ)) - Real.log (Real.log x) -
        (Real.eulerMascheroniConstant +
          ∑' p : Nat.Primes, (Real.log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ)))| ≤
      4 / (Real.log x) ^ 3 := by
  have hupper := mawia_reciprocal_sum_upper_bound_large x hlarge
  have hlower := mawia_reciprocal_sum_lower_bound_large x hlarge
  rw [abs_le]
  constructor <;> linarith

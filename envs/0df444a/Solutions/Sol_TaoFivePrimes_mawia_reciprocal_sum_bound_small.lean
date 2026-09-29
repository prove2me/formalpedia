-- Prove2me | solution 1 for TaoFivePrimes.mawia_reciprocal_sum_bound_small
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-25T14:26:30.586648+00:00
-- url     : https://prove2.me/submissions/7db5507e-3518-482f-9908-4845d0ea4365
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_TaoFivePrimes_mawia_reciprocal_sum_upper_bound_small
import Theorems.Thm_TaoFivePrimes_mawia_reciprocal_sum_lower_bound_small
import Mathlib

open TaoFivePrimes

theorem solution (x : ℝ) (hx : 2 ≤ x) (hsmall : x ≤ 10 ^ 8) :
    |(∑ p ∈ Nat.primesLE ⌊x⌋₊, 1 / (p : ℝ)) - Real.log (Real.log x) -
        (Real.eulerMascheroniConstant +
          ∑' p : Nat.Primes, (Real.log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ)))| ≤
      4 / (Real.log x) ^ 3 := by
  have hupper := mawia_reciprocal_sum_upper_bound_small x hx hsmall
  have hlower := mawia_reciprocal_sum_lower_bound_small x hx hsmall
  rw [abs_le]
  constructor <;> linarith
-- Prove2me | solution 1 for TaoFivePrimes.mawia_reciprocal_sum_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-25T12:40:26.107195+00:00
-- url     : https://prove2.me/submissions/26d686fd-1046-47f4-bb64-f0bb4feae38f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_TaoFivePrimes_mawia_reciprocal_sum_bound_small
import Theorems.Thm_TaoFivePrimes_mawia_reciprocal_sum_bound_large
import Mathlib

open TaoFivePrimes

theorem solution (x : ℝ) (hx : 2 ≤ x) :
    |(∑ p ∈ Nat.primesLE ⌊x⌋₊, 1 / (p : ℝ)) - Real.log (Real.log x) -
        (Real.eulerMascheroniConstant +
          ∑' p : Nat.Primes, (Real.log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ)))| ≤
      4 / (Real.log x) ^ 3 := by
  rcases le_total x (10 ^ 8) with hsmall | hlarge
  · exact mawia_reciprocal_sum_bound_small x hx hsmall
  · exact mawia_reciprocal_sum_bound_large x hlarge
-- Prove2me | solution 1 for OddPerfectNumber.geom_ratio_lower_three_ge_four
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-14T02:40:59.22661+00:00
-- url     : https://prove2.me/submissions/2cb5ba10-b14e-4a06-91ae-8290a17d3d03

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_mul_sub_one

theorem solution (a : Nat) (ha : 4 ≤ a) :
    121 * 3 ^ a ≤
      81 * (∑ i ∈ Finset.range (a + 1), 3 ^ i) := by
  have hgeom := OddPerfectNumber.geom_mul_sub_one 3 (a + 1) (by norm_num)
  rw [pow_succ] at hgeom
  have hpow : 81 ≤ 3 ^ a := by
    exact Nat.pow_le_pow_right (by norm_num : 0 < 3) ha
  omega

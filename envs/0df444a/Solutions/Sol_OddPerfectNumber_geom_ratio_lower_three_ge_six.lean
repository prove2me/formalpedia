-- Prove2me | solution 1 for OddPerfectNumber.geom_ratio_lower_three_ge_six
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-13T23:47:07.826183+00:00
-- url     : https://prove2.me/submissions/25bf56c3-1303-4e19-96b0-98cdc0d04148

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_mul_sub_one

theorem solution (a : Nat) (ha : 6 ≤ a) :
    1093 * 3 ^ a ≤
      729 * (∑ i ∈ Finset.range (a + 1), 3 ^ i) := by
  have hgeom := OddPerfectNumber.geom_mul_sub_one 3 (a + 1) (by norm_num)
  rw [pow_succ] at hgeom
  have hpow : 729 ≤ 3 ^ a := by
    exact Nat.pow_le_pow_right (by norm_num : 0 < 3) ha
  omega

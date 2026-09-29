-- Prove2me | solution 1 for OddPerfectNumber.geom_ratio_lower_nineteen_ge_four
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-14T11:07:17.987221+00:00
-- url     : https://prove2.me/submissions/e3481b05-766a-4d75-8668-d9c7b3d951c0

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_mul_sub_one

theorem solution (c : Nat) (hc : 4 ≤ c) :
    137561 * 19 ^ c <=
      130321 * (∑ i ∈ Finset.range (c + 1), 19 ^ i) := by
  have hgeom := OddPerfectNumber.geom_mul_sub_one 19 (c + 1) (by norm_num)
  rw [pow_succ] at hgeom
  have hpow : 130321 ≤ 19 ^ c := by
    exact Nat.pow_le_pow_right (by norm_num : 0 < 19) hc
  omega

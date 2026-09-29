-- Prove2me | solution 1 for OddPerfectNumber.geom_ratio_lower_five_ge_two
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-14T02:43:00.705596+00:00
-- url     : https://prove2.me/submissions/b55a49b6-9ade-4a50-83a9-2bf747e3b1eb

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_mul_sub_one

theorem solution (b : Nat) (hb : 2 ≤ b) :
    31 * 5 ^ b ≤
      25 * (∑ i ∈ Finset.range (b + 1), 5 ^ i) := by
  have hgeom := OddPerfectNumber.geom_mul_sub_one 5 (b + 1) (by norm_num)
  rw [pow_succ] at hgeom
  have hpow : 25 ≤ 5 ^ b := by
    exact Nat.pow_le_pow_right (by norm_num : 0 < 5) hb
  omega

-- Prove2me | solution 1 for OddPerfectNumber.geom_ratio_lower_thirteen_ge_two
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-14T02:43:10.50522+00:00
-- url     : https://prove2.me/submissions/b8c9aa79-76f9-4d29-ba3a-77fbd727510a

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_mul_sub_one

theorem solution (c : Nat) (hc : 2 ≤ c) :
    183 * 13 ^ c ≤
      169 * (∑ i ∈ Finset.range (c + 1), 13 ^ i) := by
  have hgeom := OddPerfectNumber.geom_mul_sub_one 13 (c + 1) (by norm_num)
  rw [pow_succ] at hgeom
  have hpow : 169 ≤ 13 ^ c := by
    exact Nat.pow_le_pow_right (by norm_num : 0 < 13) hc
  omega

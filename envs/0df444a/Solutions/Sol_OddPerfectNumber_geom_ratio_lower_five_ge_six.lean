-- Prove2me | solution 1 for OddPerfectNumber.geom_ratio_lower_five_ge_six
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-14T03:12:47.074122+00:00
-- url     : https://prove2.me/submissions/ee17eeed-4e12-4152-bb8c-20bb0e28b479

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_mul_sub_one

theorem solution (b : Nat) (hb : 6 ≤ b) :
    3906 * 5 ^ b ≤
      3125 * (∑ i ∈ Finset.range (b + 1), 5 ^ i) := by
  have hgeom := OddPerfectNumber.geom_mul_sub_one 5 (b + 1) (by norm_num)
  rw [pow_succ] at hgeom
  have hpow : 3125 ≤ 5 ^ b := by
    have hb5 : 5 ≤ b := by omega
    simpa using (Nat.pow_le_pow_right (by norm_num : 0 < 5) hb5)
  omega

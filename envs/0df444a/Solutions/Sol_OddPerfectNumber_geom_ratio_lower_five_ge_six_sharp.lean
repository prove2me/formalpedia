-- Prove2me | solution 1 for OddPerfectNumber.geom_ratio_lower_five_ge_six_sharp
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-14T16:04:02.15253+00:00
-- url     : https://prove2.me/submissions/8a1d5f0d-c876-4e89-bf83-bd2616aae826

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_mul_sub_one

theorem solution (b : Nat) (hb : 6 ≤ b) :
    19531 * 5 ^ b ≤
      15625 * (∑ i ∈ Finset.range (b + 1), 5 ^ i) := by
  have hgeom := OddPerfectNumber.geom_mul_sub_one 5 (b + 1) (by norm_num)
  rw [pow_succ] at hgeom
  have hpow : 15625 ≤ 5 ^ b := by
    simpa using (Nat.pow_le_pow_right (by norm_num : 0 < 5) hb)
  omega

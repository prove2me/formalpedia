-- Prove2me | solution 1 for OddPerfectNumber.geom_ratio_lower_263_ge_two
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-14T23:52:23.96256+00:00
-- url     : https://prove2.me/submissions/a2aabd61-a844-4f57-b3fe-c334b8223ba9

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_mul_sub_one

theorem solution (e : Nat) (he : 2 ≤ e) :
    69433 * 263 ^ e ≤
      69169 * (∑ i ∈ Finset.range (e + 1), 263 ^ i) := by
  have hgeom := OddPerfectNumber.geom_mul_sub_one 263 (e + 1) (by norm_num)
  rw [pow_succ] at hgeom
  have hpow : 69169 ≤ 263 ^ e := by
    exact Nat.pow_le_pow_right (by norm_num : 0 < 263) he
  omega

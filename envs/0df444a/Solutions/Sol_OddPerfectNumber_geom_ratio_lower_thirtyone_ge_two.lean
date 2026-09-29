-- Prove2me | solution 1 for OddPerfectNumber.geom_ratio_lower_thirtyone_ge_two
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-13T23:49:33.979173+00:00
-- url     : https://prove2.me/submissions/e98f98ab-4ec3-409c-8657-ddcb1cc57383

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_mul_sub_one

theorem solution (e : Nat) (he : 2 ≤ e) :
    993 * 31 ^ e ≤
      961 * (∑ i ∈ Finset.range (e + 1), 31 ^ i) := by
  have hgeom := OddPerfectNumber.geom_mul_sub_one 31 (e + 1) (by norm_num)
  rw [pow_succ] at hgeom
  have hpow : 961 ≤ 31 ^ e := by
    exact Nat.pow_le_pow_right (by norm_num : 0 < 31) he
  omega

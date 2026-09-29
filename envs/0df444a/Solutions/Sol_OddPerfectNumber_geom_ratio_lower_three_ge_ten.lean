-- Prove2me | solution 1 for OddPerfectNumber.geom_ratio_lower_three_ge_ten
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-14T23:50:15.494393+00:00
-- url     : https://prove2.me/submissions/193e5042-d637-42b0-9d74-7d2574355c69

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_mul_sub_one

theorem solution (a : Nat) (ha : 10 ≤ a) :
    88573 * 3 ^ a ≤
      59049 * (∑ i ∈ Finset.range (a + 1), 3 ^ i) := by
  have hgeom := OddPerfectNumber.geom_mul_sub_one 3 (a + 1) (by norm_num)
  rw [pow_succ] at hgeom
  have hpow : 59049 ≤ 3 ^ a := by
    exact Nat.pow_le_pow_right (by norm_num : 0 < 3) ha
  omega

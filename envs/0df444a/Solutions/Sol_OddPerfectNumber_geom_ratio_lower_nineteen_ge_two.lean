-- Prove2me | solution 1 for OddPerfectNumber.geom_ratio_lower_nineteen_ge_two
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-13T23:47:43.411672+00:00
-- url     : https://prove2.me/submissions/e83b4a64-db6f-413a-88fd-6473425ab6d5

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_mul_sub_one

theorem solution (c : Nat) (hc : 2 ≤ c) :
    381 * 19 ^ c ≤
      361 * (∑ i ∈ Finset.range (c + 1), 19 ^ i) := by
  have hgeom := OddPerfectNumber.geom_mul_sub_one 19 (c + 1) (by norm_num)
  rw [pow_succ] at hgeom
  have hpow : 361 ≤ 19 ^ c := by
    exact Nat.pow_le_pow_right (by norm_num : 0 < 19) hc
  omega

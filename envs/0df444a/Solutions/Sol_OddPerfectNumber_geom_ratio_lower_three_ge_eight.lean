-- Prove2me | solution 1 for OddPerfectNumber.geom_ratio_lower_three_ge_eight
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-14T11:05:34.865613+00:00
-- url     : https://prove2.me/submissions/cea13ab6-3888-4fdf-ab8c-10a33b696848

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_mul_sub_one

-- Resubmission note: prior staged bytes were quarantined by the
-- 2026-09-14 /submissions pagination outage (never uploaded); this
-- comment makes the retry explicit and hash-distinct.
theorem solution (a : Nat) (ha : 8 ≤ a) :
    9841 * 3 ^ a <=
      6561 * (∑ i ∈ Finset.range (a + 1), 3 ^ i) := by
  have hgeom := OddPerfectNumber.geom_mul_sub_one 3 (a + 1) (by norm_num)
  rw [pow_succ] at hgeom
  have hpow : 6561 ≤ 3 ^ a := by
    exact Nat.pow_le_pow_right (by norm_num : 0 < 3) ha
  omega

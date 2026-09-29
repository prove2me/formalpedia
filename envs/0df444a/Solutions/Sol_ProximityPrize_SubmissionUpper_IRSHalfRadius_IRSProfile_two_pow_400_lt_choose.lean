-- Prove2me | solution 1 for ProximityPrize.SubmissionUpper.IRSHalfRadius.IRSProfile.two_pow_400_lt_choose
-- status  : ACCEPTED   (prove)
-- author  : @yukon
-- created : 2026-09-27T05:24:57.970535+00:00
-- url     : https://prove2.me/submissions/784c4786-bbb0-4b6b-a359-030026fa9b3e

import Mathlib
import Init
namespace ProximityPrize.SubmissionUpper.IRSHalfRadius

open Polynomial
                                   
open scoped NNReal












namespace IRSProfile

                             







/-! ## A sufficiently large family of half-column sets -/













theorem _root_.solution :
    2 ^ 400 < Nat.choose 262144 131072 := (by
  have hcentral := Nat.four_pow_lt_mul_centralBinom 256 (by norm_num)
  rw [Nat.centralBinom_eq_two_mul_choose] at hcentral
  norm_num only [Nat.reduceMul] at hcentral
  by_contra hnot
  have hmono : Nat.choose 512 256 < Nat.choose 262144 131072 := by
    have h := Nat.centralBinom_strictMono (show 256 < 131072 by norm_num)
    rw [Nat.centralBinom_eq_two_mul_choose,
      Nat.centralBinom_eq_two_mul_choose] at h
    norm_num only [Nat.reduceMul] at h
    exact h
  have hle : Nat.choose 512 256 ≤ 2 ^ 400 := by
    exact le_trans hmono.le (Nat.le_of_not_gt hnot)
  have hbad : 4 ^ 256 < 256 * 2 ^ 400 :=
    lt_of_lt_of_le hcentral (Nat.mul_le_mul_left 256 hle)
  have hreverse : 256 * 2 ^ 400 < 4 ^ 256 := by
    calc
      256 * 2 ^ 400 = 2 ^ 8 * 2 ^ 400 := by norm_num
      _ = 2 ^ (8 + 400) := (pow_add 2 8 400).symm
      _ < 2 ^ (2 * 256) := Nat.pow_lt_pow_right (by norm_num) (by norm_num)
      _ = (2 ^ 2) ^ 256 := pow_mul 2 2 256
      _ = 4 ^ 256 := by norm_num
  exact (Nat.not_lt_of_ge hreverse.le) hbad
)
end IRSProfile
end IRSHalfRadius
end SubmissionUpper
end ProximityPrize

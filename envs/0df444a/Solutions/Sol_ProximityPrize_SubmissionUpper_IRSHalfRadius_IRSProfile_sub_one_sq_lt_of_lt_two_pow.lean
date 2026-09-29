-- Prove2me | solution 1 for ProximityPrize.SubmissionUpper.IRSHalfRadius.IRSProfile.sub_one_sq_lt_of_lt_two_pow
-- status  : ACCEPTED   (prove)
-- author  : @yukon
-- created : 2026-09-27T05:26:35.175404+00:00
-- url     : https://prove2.me/submissions/3a4d96ba-2dc9-46aa-8349-e9d6a7317693

import Mathlib
import Init
namespace ProximityPrize.SubmissionUpper.IRSHalfRadius

open Polynomial
                                   
open scoped NNReal












namespace IRSProfile

                             







/-! ## A sufficiently large family of half-column sets -/
















theorem _root_.solution
    {q N : Nat} (hq : q < 2 ^ 186) (hN : 2 ^ 400 < N) :
    (q - 1) ^ 2 < N := (by
  have hfield : q - 1 < 2 ^ 186 :=
    lt_of_le_of_lt (Nat.sub_le _ _) hq
  have hfieldSq : (q - 1) ^ 2 < (2 ^ 186) ^ 2 :=
    Nat.pow_lt_pow_left hfield (by norm_num)
  calc
    (q - 1) ^ 2 < (2 ^ 186) ^ 2 := hfieldSq
    _ = 2 ^ (186 * 2) := (pow_mul 2 186 2).symm
    _ = 2 ^ 372 := by norm_num
    _ < 2 ^ 400 := Nat.pow_lt_pow_right (by norm_num) (by norm_num)
    _ < N := hN
)
end IRSProfile
end IRSHalfRadius
end SubmissionUpper
end ProximityPrize

-- Prove2me | solution 1 for ThreeSum.KaratsubaInterface.time_with_linear_fifth_power
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:16:21.018898+00:00
-- url     : https://prove2.me/submissions/9b3a71c4-02a7-4a1b-8adf-5ebef0a8712e

import Definitions.Def_Submission_ThreeSum_LightKaratsuba
import Mathlib.Data.Nat.Log
import Definitions.Def_Submission_ThreeSum_KaratsubaInterface
import Theorems.Thm_ThreeSum_KaratsubaInterface_time_with_linear_bound

set_option autoImplicit false
open ThreeSum ThreeSum.KaratsubaInterface
open ThreeSum.Karatsuba ThreeSum.LightKaratsuba Polynomial
namespace ThreeSum.KaratsubaInterface
theorem _root_.solution (k c : ℕ) :
    (time k + c * 2 ^ k + c) ^ 5 ≤ (2530 + 2 * c) ^ 5 * (2 ^ k) ^ 8 := by
  have ht := Nat.pow_le_pow_left (time_with_linear_bound k c) 5
  have hp := Nat.pow_le_pow_left (show (3 : ℕ) ^ 5 ≤ 2 ^ 8 by norm_num) k
  calc
    _ ≤ ((2530 + 2 * c) * 3 ^ k) ^ 5 := ht
    _ = (2530 + 2 * c) ^ 5 * (3 ^ 5) ^ k := by
      rw [mul_pow, ← pow_mul, Nat.mul_comm k 5, pow_mul]
    _ ≤ (2530 + 2 * c) ^ 5 * (2 ^ 8) ^ k := Nat.mul_le_mul_left _ hp
    _ = _ := by rw [← pow_mul, Nat.mul_comm 8 k, pow_mul]
end ThreeSum.KaratsubaInterface

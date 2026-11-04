-- Prove2me | solution 1 for ThreeSum.LightKaratsuba.time_fifth_power
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:24:29.445978+00:00
-- url     : https://prove2.me/submissions/0e5048bf-e5b1-4ee0-af0d-bcd3dbc61203

import Definitions.Def_Submission_ThreeSum_KaratsubaBounds
import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Logs
import Definitions.Def_Submission_ThreeSum_LightKaratsuba
import Theorems.Thm_ThreeSum_LightKaratsuba_time_le

set_option autoImplicit false
open ThreeSum ThreeSum.LightKaratsuba
open Light
open ThreeSum.Karatsuba
open Polynomial
namespace ThreeSum.LightKaratsuba
theorem _root_.solution (k : ℕ) :
    time k ^ 5 ≤ 2530 ^ 5 * (2 ^ k) ^ 8 := by
  have ht := Nat.pow_le_pow_left (time_le k) 5
  have hp : (3 : ℕ) ^ 5 ≤ 2 ^ 8 := by norm_num
  have hp' := Nat.pow_le_pow_left hp k
  calc
    _ ≤ (2530 * 3 ^ k) ^ 5 := ht
    _ = 2530 ^ 5 * (3 ^ 5) ^ k := by rw [mul_pow, ← pow_mul, Nat.mul_comm k 5, pow_mul]
    _ ≤ 2530 ^ 5 * (2 ^ 8) ^ k := Nat.mul_le_mul_left _ hp'
    _ = _ := by rw [← pow_mul, Nat.mul_comm 8 k, pow_mul]
end ThreeSum.LightKaratsuba

-- Prove2me | solution 1 for ThreeSum.KaratsubaInterface.time_with_linear_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:57:44.284813+00:00
-- url     : https://prove2.me/submissions/e205c606-159c-4ad4-8f20-9bbbcb727a12

import Definitions.Def_Submission_ThreeSum_LightKaratsuba
import Mathlib.Data.Nat.Log
import Definitions.Def_Submission_ThreeSum_KaratsubaInterface
import Theorems.Thm_ThreeSum_LightKaratsuba_time_le


set_option autoImplicit false
open ThreeSum ThreeSum.KaratsubaInterface
open ThreeSum.Karatsuba ThreeSum.LightKaratsuba Polynomial
namespace ThreeSum.KaratsubaInterface
theorem _root_.solution (k c : ℕ) :
    time k + c * 2 ^ k + c ≤ (2530 + 2 * c) * 3 ^ k := by
  have ht := time_le k
  have hn : (2 : ℕ) ^ k ≤ 3 ^ k := Nat.pow_le_pow_left (by decide) k
  have hmc := Nat.mul_le_mul_left c hn
  have hc := Nat.mul_le_mul_left c (Nat.one_le_pow k 3 (by decide))
  nlinarith
end ThreeSum.KaratsubaInterface

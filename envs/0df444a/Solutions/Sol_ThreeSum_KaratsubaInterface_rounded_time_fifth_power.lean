-- Prove2me | solution 1 for ThreeSum.KaratsubaInterface.rounded_time_fifth_power
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:22:53.033937+00:00
-- url     : https://prove2.me/submissions/318acb94-3b72-484d-b7f2-a4dbde995306

import Definitions.Def_Submission_ThreeSum_LightKaratsuba
import Mathlib.Data.Nat.Log
import Definitions.Def_Submission_ThreeSum_KaratsubaInterface
import Definitions.Def_WeightedCache3SUM_Alias_44fe933b0cad9ef5
import Theorems.Thm_ThreeSum_KaratsubaInterface_time_with_linear_fifth_power

set_option autoImplicit false
open ThreeSum ThreeSum.KaratsubaInterface
open ThreeSum.Karatsuba ThreeSum.LightKaratsuba Polynomial
namespace ThreeSum.KaratsubaInterface
theorem _root_.solution {p : ℕ} (hp : 0 < p) (c : ℕ) :
    (time (Nat.clog 2 p) + c * capacity p + c) ^ 5 ≤
      ((2530 + 2 * c) ^ 5 * 2 ^ 8) * p ^ 8 := by
  have ht := time_with_linear_fifth_power (Nat.clog 2 p) c
  have hn := Nat.pow_le_pow_left (capacity_lt_twice hp).le 8
  calc
    _ ≤ (2530 + 2 * c) ^ 5 * capacity p ^ 8 := ht
    _ ≤ (2530 + 2 * c) ^ 5 * (2 * p) ^ 8 := Nat.mul_le_mul_left _ hn
    _ = _ := by rw [mul_pow, mul_assoc]
end ThreeSum.KaratsubaInterface

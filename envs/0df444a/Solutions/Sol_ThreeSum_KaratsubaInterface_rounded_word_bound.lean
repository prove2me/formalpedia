-- Prove2me | solution 1 for ThreeSum.KaratsubaInterface.rounded_word_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:24:31.079196+00:00
-- url     : https://prove2.me/submissions/ccb2ade8-e2ba-4ba5-93a2-704bea21c6f7

import Definitions.Def_Submission_ThreeSum_LightKaratsuba
import Mathlib.Data.Nat.Log
import Definitions.Def_Submission_ThreeSum_KaratsubaInterface
import Definitions.Def_WeightedCache3SUM_Alias_44fe933b0cad9ef5

set_option autoImplicit false
open ThreeSum ThreeSum.KaratsubaInterface
open ThreeSum.Karatsuba ThreeSum.LightKaratsuba Polynomial
namespace ThreeSum.KaratsubaInterface
theorem _root_.solution {p : ℕ} (hp : 0 < p) (U : ℕ) :
    wordBound (capacity p) U ≤ 1024 * p ^ 3 * (U + 1) ^ 2 := by
  have hn := Nat.pow_le_pow_left (capacity_lt_twice hp).le 3
  unfold wordBound
  calc
    _ ≤ 128 * (2 * p) ^ 3 * (U + 1) ^ 2 :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hn)
    _ = _ := by ring
end ThreeSum.KaratsubaInterface

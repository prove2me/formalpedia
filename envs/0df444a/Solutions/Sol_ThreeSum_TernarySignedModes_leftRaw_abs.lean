-- Prove2me | solution 1 for ThreeSum.TernarySignedModes.leftRaw_abs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:42:21.422386+00:00
-- url     : https://prove2.me/submissions/1cdf8152-dcca-4cf4-8381-148c2acc8c10

import Definitions.Def_Submission_ThreeSum_TernarySignedReduction
import Mathlib.Data.Int.Lemmas
import Definitions.Def_Submission_ThreeSum_TernarySignedModes
import Theorems.Thm_ThreeSum_TernarySignedDigits_carryNat_zero
import Theorems.Thm_ThreeSum_TernarySignedDigits_digit_lt
import Theorems.Thm_ThreeSum_TernarySignedReduction_mem_carryCatalog
attribute [local simp] ThreeSum.TernarySignedDigits.carryNat_zero
attribute [local simp] ThreeSum.TernarySignedReduction.mem_carryCatalog



set_option autoImplicit false
open ThreeSum ThreeSum.TernarySignedModes
open TernarySignedDigits TernarySignedReduction Finset
namespace ThreeSum.TernarySignedModes
theorem _root_.solution {U radix J : ℕ} (hb : 1 < radix) (b : ℤ) (k : Coordinate J) :
    |leftRaw U radix J b k| ≤ (radix : ℤ) := by
  cases k with
  | inl j =>
    simp only [leftRaw,abs_neg,Int.abs_natCast]
    exact_mod_cast (digit_lt (by omega) _ _).le
  | inr t => cases t <;> norm_num [leftRaw] <;> omega
end ThreeSum.TernarySignedModes

-- Prove2me | solution 1 for ThreeSum.TernarySignedModes.rawMode_abs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:42:44.040026+00:00
-- url     : https://prove2.me/submissions/64b27582-b8b6-448b-975f-e7616811e9cd

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
theorem _root_.solution {U radix J : ℕ} (hb : 1 < radix) (b c : ℤ) (k : Coordinate J) :
    |rawMode U radix J b c k| ≤ (radix : ℤ) := by
  cases k with
  | inl j =>
    have hx : (digit radix (shiftOne U b) j : ℤ) < radix := by
      exact_mod_cast digit_lt (by omega : 0 < radix) _ _
    have hy : (digit radix (shiftTwo U c) j : ℤ) < radix := by
      exact_mod_cast digit_lt (by omega : 0 < radix) _ _
    have hx0 : (0 : ℤ) ≤ digit radix (shiftOne U b) j := by positivity
    have hy0 : (0 : ℤ) ≤ digit radix (shiftTwo U c) j := by positivity
    simp only [rawMode,leftRaw,rightRaw]
    exact abs_le.mpr ⟨by omega,by omega⟩
  | inr t => cases t <;> norm_num [rawMode,leftRaw,rightRaw] <;> omega
end ThreeSum.TernarySignedModes

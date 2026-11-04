-- Prove2me | solution 1 for ThreeSum.TernarySignedModes.requesterRaw_abs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:43:01.402868+00:00
-- url     : https://prove2.me/submissions/1bc3a1d0-50ae-453d-a11d-fd0c94b4682b

import Definitions.Def_Submission_ThreeSum_TernarySignedReduction
import Mathlib.Data.Int.Lemmas
import Definitions.Def_Submission_ThreeSum_TernarySignedModes
import Theorems.Thm_ThreeSum_TernarySignedModes_carryAt_bounds
import Theorems.Thm_ThreeSum_TernarySignedDigits_carryNat_zero
import Theorems.Thm_ThreeSum_TernarySignedDigits_digit_lt
import Theorems.Thm_ThreeSum_TernarySignedReduction_mem_carryCatalog
attribute [local simp] ThreeSum.TernarySignedDigits.carryNat_zero
attribute [local simp] ThreeSum.TernarySignedReduction.mem_carryCatalog



set_option autoImplicit false
open ThreeSum ThreeSum.TernarySignedModes
open TernarySignedDigits TernarySignedReduction Finset
namespace ThreeSum.TernarySignedModes
theorem _root_.solution {U radix J : ℕ} (hb : 1 < radix)
    (a : ℤ) (c : CarryWord J) (k : Coordinate J) :
    |requesterRaw U radix J a c k| ≤ (radix : ℤ) := by
  cases k with
  | inl j =>
    have hd : (digit radix (shiftOne U a) j : ℤ) < radix := by
      exact_mod_cast digit_lt (by omega : 0 < radix) _ _
    have hd0 : (0 : ℤ) ≤ digit radix (shiftOne U a) j := by positivity
    have h0 := carryAt_bounds c j
    have h1 := carryAt_bounds c (j+1)
    simp only [requesterRaw]
    apply abs_le.mpr
    constructor <;> nlinarith
  | inr t => simp only [requesterRaw,abs_one]; exact_mod_cast (by omega : 1 ≤ radix)
end ThreeSum.TernarySignedModes

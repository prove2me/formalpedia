-- Prove2me | solution 1 for ThreeSum.TernarySignedReduction.shifted_addition_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:40:39.803327+00:00
-- url     : https://prove2.me/submissions/f16b5a3a-8354-4f8a-98b4-ace1629761a0

import Definitions.Def_Submission_ThreeSum_TernarySignedDigits
import Mathlib.Data.ZMod.Basic
import Definitions.Def_Submission_ThreeSum_TernarySignedReduction
import Theorems.Thm_ThreeSum_TernarySignedReduction_shiftOne_cast
import Theorems.Thm_ThreeSum_TernarySignedReduction_shiftTwo_cast

set_option autoImplicit false
open ThreeSum ThreeSum.TernarySignedReduction
open TernarySignedDigits Finset
namespace ThreeSum.TernarySignedReduction
theorem _root_.solution {U : ℕ} {a b c : ℤ}
    (ha : |a| ≤ (U : ℤ)) (hb : |b| ≤ (U : ℤ)) (hc : |c| ≤ (U : ℤ)) :
    shiftOne U b+shiftOne U a=shiftTwo U c ↔ c-b=a := by
  have hA := shiftOne_cast ha
  have hB := shiftOne_cast hb
  have hC := shiftTwo_cast hc
  constructor
  · intro h
    have hi : (shiftOne U b : ℤ)+(shiftOne U a : ℤ)=(shiftTwo U c : ℤ) := by exact_mod_cast h
    omega
  · intro h
    have hi : (shiftOne U b : ℤ)+(shiftOne U a : ℤ)=(shiftTwo U c : ℤ) := by omega
    exact_mod_cast hi
end ThreeSum.TernarySignedReduction

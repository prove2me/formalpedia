-- Prove2me | solution 1 for ThreeSum.TernaryCarryCode.codeOfCarry_digit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:24:46.69214+00:00
-- url     : https://prove2.me/submissions/a7c99fc5-0971-4e05-85cd-46f3aed8b87d

import Definitions.Def_Submission_ThreeSum_TernarySignedReduction
import Definitions.Def_Submission_ThreeSum_TernarySignedModes
import Mathlib.Data.Nat.Digits.Lemmas
import Definitions.Def_Submission_ThreeSumApsp_Util_List
import Definitions.Def_Submission_ThreeSum_TernaryCarryCode
import Theorems.Thm_ThreeSum_TernaryCarryCode_digit_ofDigits
import Theorems.Thm_ThreeSum_TernarySignedDigits_carryNat_zero
import Theorems.Thm_ThreeSum_TernarySignedReduction_mem_carryCatalog
attribute [local simp] ThreeSum.TernarySignedDigits.carryNat_zero
attribute [local simp] ThreeSum.TernarySignedReduction.mem_carryCatalog



set_option autoImplicit false
open ThreeSum ThreeSum.TernaryCarryCode
open TernarySignedDigits TernarySignedReduction Finset
namespace ThreeSum.TernaryCarryCode
theorem _root_.solution {J : ℕ} (c : CarryWord J) (i : Fin J) :
    digit 2 (codeOfCarry c) i.val=(c i.castSucc).val := by
  unfold codeOfCarry
  rw [digit_ofDigits (by decide)]
  · rw [List.getD_eq_getElem _ _ (by simpa using i.isLt)]
    simp
  · intro x hx
    obtain ⟨j,hj⟩ := List.mem_ofFn.mp hx
    rw [← hj]
    exact (c j.castSucc).isLt
end ThreeSum.TernaryCarryCode

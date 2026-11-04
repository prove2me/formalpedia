-- Prove2me | solution 1 for ThreeSum.TernaryCarryCode.carryFromCode_code
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:28:43.892111+00:00
-- url     : https://prove2.me/submissions/7a7173fc-772a-480f-a991-a3364b028da1

import Definitions.Def_Submission_ThreeSum_TernarySignedReduction
import Definitions.Def_Submission_ThreeSum_TernarySignedModes
import Mathlib.Data.Nat.Digits.Lemmas
import Definitions.Def_Submission_ThreeSumApsp_Util_List
import Definitions.Def_Submission_ThreeSum_TernaryCarryCode
import Theorems.Thm_ThreeSum_TernaryCarryCode_codeOfCarry_digit
import Theorems.Thm_ThreeSum_TernarySignedDigits_carryNat_zero
import Theorems.Thm_ThreeSum_TernarySignedReduction_mem_carryCatalog
import Theorems.Thm_ThreeSum_TernarySignedReduction_valid_last
attribute [local simp] ThreeSum.TernarySignedDigits.carryNat_zero
attribute [local simp] ThreeSum.TernarySignedReduction.mem_carryCatalog



set_option autoImplicit false
open ThreeSum ThreeSum.TernaryCarryCode
open TernarySignedDigits TernarySignedReduction Finset
namespace ThreeSum.TernaryCarryCode
theorem _root_.solution {J : ℕ} {c : CarryWord J} (hc : ValidCarry c) :
    carryFromCode J (codeOfCarry c)=c := by
  funext i
  by_cases hi : i.val<J
  · apply Fin.ext
    simp only [carryFromCode,dif_pos hi]
    have h := codeOfCarry_digit c ⟨i.val,hi⟩
    simpa using h
  · have he : i=Fin.last J := by apply Fin.ext; simp; omega
    rw [he,valid_last hc]
    simp [carryFromCode]
end ThreeSum.TernaryCarryCode

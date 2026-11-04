-- Prove2me | solution 1 for ThreeSum.TernaryCarryCode.carryCatalog_eq_codes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:33:23.163202+00:00
-- url     : https://prove2.me/submissions/0adaa2df-809c-422e-9c49-b11108e622b1

import Definitions.Def_Submission_ThreeSum_TernarySignedReduction
import Definitions.Def_Submission_ThreeSum_TernarySignedModes
import Mathlib.Data.Nat.Digits.Lemmas
import Definitions.Def_Submission_ThreeSumApsp_Util_List
import Definitions.Def_Submission_ThreeSum_TernaryCarryCode
import Theorems.Thm_ThreeSum_TernaryCarryCode_codeOfCarry_lt
import Theorems.Thm_ThreeSum_TernaryCarryCode_carryFromCode_code
import Theorems.Thm_ThreeSum_TernaryCarryCode_codeOfCarry_initial
import Theorems.Thm_ThreeSum_TernaryCarryCode_carryFromCode_valid
import Theorems.Thm_ThreeSum_TernarySignedReduction_mem_carryCatalog
attribute [local simp] ThreeSum.TernarySignedReduction.mem_carryCatalog



set_option autoImplicit false
open ThreeSum ThreeSum.TernaryCarryCode
open TernarySignedDigits TernarySignedReduction Finset
namespace ThreeSum.TernaryCarryCode
theorem _root_.solution (J : ℕ) :
    carryCatalog J=(codeCatalog J).image (carryFromCode J) := by
  ext c
  constructor
  · intro hc
    have hv := (mem_carryCatalog c).mp hc
    apply mem_image.mpr
    exact ⟨codeOfCarry c,mem_filter.mpr ⟨mem_range.mpr (codeOfCarry_lt c),codeOfCarry_initial hv⟩,
      carryFromCode_code hv⟩
  · intro hc
    obtain ⟨q,hq,rfl⟩ := mem_image.mp hc
    exact (mem_carryCatalog _).mpr (carryFromCode_valid (mem_filter.mp hq).2)
end ThreeSum.TernaryCarryCode

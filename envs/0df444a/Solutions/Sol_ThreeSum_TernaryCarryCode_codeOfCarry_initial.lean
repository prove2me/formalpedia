-- Prove2me | solution 1 for ThreeSum.TernaryCarryCode.codeOfCarry_initial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:28:47.568673+00:00
-- url     : https://prove2.me/submissions/859be2bf-c40f-4128-a300-610c6fc19c3e

import Definitions.Def_Submission_ThreeSum_TernarySignedReduction
import Definitions.Def_Submission_ThreeSum_TernarySignedModes
import Mathlib.Data.Nat.Digits.Lemmas
import Definitions.Def_Submission_ThreeSumApsp_Util_List
import Definitions.Def_Submission_ThreeSum_TernaryCarryCode
import Theorems.Thm_ThreeSum_TernaryCarryCode_codeOfCarry_digit
import Theorems.Thm_ThreeSum_TernarySignedDigits_carryNat_zero
import Theorems.Thm_ThreeSum_TernarySignedReduction_mem_carryCatalog
attribute [local simp] ThreeSum.TernarySignedDigits.carryNat_zero
attribute [local simp] ThreeSum.TernarySignedReduction.mem_carryCatalog



set_option autoImplicit false
open ThreeSum ThreeSum.TernaryCarryCode
open TernarySignedDigits TernarySignedReduction Finset
namespace ThreeSum.TernaryCarryCode
theorem _root_.solution {J : ℕ} {c : CarryWord J} (hc : ValidCarry c) :
    digit 2 (codeOfCarry c) 0=0 := by
  by_cases hJ : 0<J
  · have h := codeOfCarry_digit c ⟨0,hJ⟩
    have hz := hc.1
    simp only [carryAt,show 0<J+1 by omega,dif_pos] at hz
    rw [h]
    exact Int.ofNat_inj.mp hz
  · have hJ0 : J=0 := by omega
    subst J
    simp [codeOfCarry,digit,quotient]
end ThreeSum.TernaryCarryCode

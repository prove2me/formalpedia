-- Prove2me | solution 1 for ThreeSum.TernaryCarryCode.codeOfCarry_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:09:01.888446+00:00
-- url     : https://prove2.me/submissions/4b9490fe-de6a-4122-a9be-5eb2389662b1

import Definitions.Def_Submission_ThreeSum_TernarySignedReduction
import Definitions.Def_Submission_ThreeSum_TernarySignedModes
import Mathlib.Data.Nat.Digits.Lemmas
import Definitions.Def_Submission_ThreeSumApsp_Util_List
import Definitions.Def_Submission_ThreeSum_TernaryCarryCode
import Theorems.Thm_ThreeSum_TernarySignedDigits_carryNat_zero
import Theorems.Thm_ThreeSum_TernarySignedReduction_mem_carryCatalog
attribute [local simp] ThreeSum.TernarySignedDigits.carryNat_zero
attribute [local simp] ThreeSum.TernarySignedReduction.mem_carryCatalog



set_option autoImplicit false
open ThreeSum ThreeSum.TernaryCarryCode
open TernarySignedDigits TernarySignedReduction Finset
namespace ThreeSum.TernaryCarryCode
theorem _root_.solution {J : ℕ} (c : CarryWord J) : codeOfCarry c<2^J := by
  have h := Nat.ofDigits_lt_base_pow_length (by decide : 1<(2 : ℕ))
    (l := List.ofFn fun i : Fin J => (c i.castSucc).val) (by
      intro x hx
      obtain ⟨i,hi⟩ := List.mem_ofFn.mp hx
      rw [← hi]
      exact (c i.castSucc).isLt)
  simpa only [List.length_ofFn,codeOfCarry] using h
end ThreeSum.TernaryCarryCode

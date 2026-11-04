-- Prove2me | solution 1 for ThreeSum.TernaryCarryCode.carryFromCode_valid
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:20:31.510399+00:00
-- url     : https://prove2.me/submissions/542ab01a-1388-4a33-a46e-3e479a6e53cc

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
theorem _root_.solution {J q : ℕ} (hq : digit 2 q 0=0) :
    ValidCarry (carryFromCode J q) := by
  constructor
  · simp only [carryAt,show 0<J+1 by omega,dif_pos,carryFromCode]
    split_ifs <;> simp [hq]
  · simp [carryAt,carryFromCode]
end ThreeSum.TernaryCarryCode

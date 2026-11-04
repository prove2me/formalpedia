-- Prove2me | solution 1 for ThreeSum.TernarySignedReduction.valid_last
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:41:45.254416+00:00
-- url     : https://prove2.me/submissions/1a8cf1bc-1d14-4007-9a3d-27dfea32d604

import Definitions.Def_Submission_ThreeSum_TernarySignedDigits
import Mathlib.Data.ZMod.Basic
import Definitions.Def_Submission_ThreeSum_TernarySignedReduction
import Theorems.Thm_ThreeSum_TernarySignedReduction_mem_carryCatalog
import Theorems.Thm_ThreeSum_TernarySignedDigits_carryNat_zero
attribute [local simp] ThreeSum.TernarySignedDigits.carryNat_zero


attribute [local simp] ThreeSum.TernarySignedReduction.mem_carryCatalog

set_option autoImplicit false
open ThreeSum ThreeSum.TernarySignedReduction
open TernarySignedDigits Finset
namespace ThreeSum.TernarySignedReduction
theorem _root_.solution {J : ℕ} {c : CarryWord J} (hc : ValidCarry c) : c (Fin.last J)=0 := by
  have h := hc.2
  simp only [carryAt,show J<J+1 by omega,dif_pos] at h
  apply Fin.ext
  exact Int.ofNat_inj.mp h
end ThreeSum.TernarySignedReduction

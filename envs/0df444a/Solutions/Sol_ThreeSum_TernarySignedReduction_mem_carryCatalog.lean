-- Prove2me | solution 1 for ThreeSum.TernarySignedReduction.mem_carryCatalog
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:40:40.894981+00:00
-- url     : https://prove2.me/submissions/0773ce90-ecee-4e56-b382-54444d866a33

import Definitions.Def_Submission_ThreeSum_TernarySignedDigits
import Mathlib.Data.ZMod.Basic
import Definitions.Def_Submission_ThreeSum_TernarySignedReduction
import Theorems.Thm_ThreeSum_TernarySignedDigits_carryNat_zero
attribute [local simp] ThreeSum.TernarySignedDigits.carryNat_zero



set_option autoImplicit false
open ThreeSum ThreeSum.TernarySignedReduction
open TernarySignedDigits Finset
namespace ThreeSum.TernarySignedReduction
theorem _root_.solution {J : ℕ} (c : CarryWord J) : c ∈ carryCatalog J ↔ ValidCarry c := by
  simp [carryCatalog]
end ThreeSum.TernarySignedReduction

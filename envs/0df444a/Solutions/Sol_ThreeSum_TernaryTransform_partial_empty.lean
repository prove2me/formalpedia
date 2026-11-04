-- Prove2me | solution 1 for ThreeSum.TernaryTransform.partial_empty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:23:36.69611+00:00
-- url     : https://prove2.me/submissions/fa8f4187-bd7d-4745-ad3c-e9b6f04cdadc

import Definitions.Def_Submission_ThreeSum_TernaryEuler
import Definitions.Def_Submission_ThreeSum_TernaryTransform
import Theorems.Thm_ThreeSum_TernaryTransform_kernel_empty
import Theorems.Thm_ThreeSum_TernaryBank_mem_bank
import Theorems.Thm_ThreeSum_TernaryBank_mem_lowerWords
import Theorems.Thm_ThreeSum_TernaryBank_mem_nearWords
attribute [local simp] ThreeSum.TernaryBank.mem_bank
attribute [local simp] ThreeSum.TernaryBank.mem_lowerWords
attribute [local simp] ThreeSum.TernaryBank.mem_nearWords



set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryTransform
open Finset
open ThreeSum.TernaryJointType ThreeSum.TernaryQuery ThreeSum.TernaryEuler
namespace ThreeSum.TernaryTransform
theorem _root_.solution {N : ℕ} (f : TritWord N → ℤ) : stageSum ∅ f = f := by
  funext R
  simp [stageSum, kernel_empty]
end ThreeSum.TernaryTransform

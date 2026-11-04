-- Prove2me | solution 1 for ThreeSum.TernaryTransform.partial_univ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:20:35.375875+00:00
-- url     : https://prove2.me/submissions/a8e0d525-e947-40a2-a6dc-f3ceebc8031c

import Definitions.Def_Submission_ThreeSum_TernaryEuler
import Definitions.Def_Submission_ThreeSum_TernaryTransform
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
theorem _root_.solution {N : ℕ} (f : TritWord N → ℤ) :
    stageSum univ f = binomialZeta f := by
  funext R
  simp [stageSum, kernel, binomialZeta, weight]
end ThreeSum.TernaryTransform

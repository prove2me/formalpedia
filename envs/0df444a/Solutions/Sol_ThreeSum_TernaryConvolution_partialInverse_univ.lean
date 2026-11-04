-- Prove2me | solution 1 for ThreeSum.TernaryConvolution.partialInverse_univ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:23:40.729354+00:00
-- url     : https://prove2.me/submissions/6c5bd6b1-a16c-4f90-80a4-0dda8dd06410

import Definitions.Def_Submission_ThreeSum_TernaryReconstruction
import Definitions.Def_Submission_ThreeSum_TernaryTransform
import Mathlib.Algebra.BigOperators.Finprod
import Definitions.Def_Submission_ThreeSum_TernaryConvolution
import Theorems.Thm_ThreeSum_TernaryBank_mem_bank
import Theorems.Thm_ThreeSum_TernaryBank_mem_lowerWords
import Theorems.Thm_ThreeSum_TernaryBank_mem_nearWords
attribute [local simp] ThreeSum.TernaryBank.mem_bank
attribute [local simp] ThreeSum.TernaryBank.mem_lowerWords
attribute [local simp] ThreeSum.TernaryBank.mem_nearWords



set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryConvolution
open Finset ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.TernaryEuler ThreeSum.TernaryQuery ThreeSum.TernaryReconstruction
set_option maxHeartbeats 2000000
namespace ThreeSum.TernaryConvolution
theorem _root_.solution {N : ℕ} (H : TritWord N → ℤ) :
    partialInverse univ H=binomialInverse H := by
  funext Q
  simp [partialInverse,partialKernel,binomialInverse,inverseWeight]
end ThreeSum.TernaryConvolution

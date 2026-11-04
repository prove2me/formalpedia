-- Prove2me | solution 1 for ThreeSum.TernaryConvolution.partialKernel_empty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:23:39.717944+00:00
-- url     : https://prove2.me/submissions/51a0049a-37f5-4beb-b36c-67344f76727d

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
theorem _root_.solution {N : ℕ} (Q A : TritWord N) :
    partialKernel ∅ Q A=if A=Q then 1 else 0 := by
  by_cases h : A=Q
  · subst A
    simp [partialKernel]
  · simp only [partialKernel,notMem_empty,↓reduceIte,h]
    obtain ⟨i,hi⟩ : ∃ i, A i≠Q i := by
      by_contra hn
      apply h
      funext i
      exact not_not.mp (not_exists.mp hn i)
    exact Finset.prod_eq_zero (mem_univ i) (by simp [hi])
end ThreeSum.TernaryConvolution

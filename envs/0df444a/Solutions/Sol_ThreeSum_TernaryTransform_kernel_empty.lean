-- Prove2me | solution 1 for ThreeSum.TernaryTransform.kernel_empty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:20:34.358435+00:00
-- url     : https://prove2.me/submissions/6e00d873-743c-4278-acaf-4140cfccebb1

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
theorem _root_.solution {N : ℕ} (R A : TritWord N) :
    kernel ∅ R A = if A = R then 1 else 0 := by
  by_cases h : A = R
  · subst A
    simp [kernel]
  · simp only [kernel, notMem_empty, ↓reduceIte, h]
    obtain ⟨i, hi⟩ : ∃ i, A i ≠ R i := by
      by_contra hn
      apply h
      funext i
      exact not_not.mp (not_exists.mp hn i)
    exact Finset.prod_eq_zero (mem_univ i) (by simp [hi])
end ThreeSum.TernaryTransform

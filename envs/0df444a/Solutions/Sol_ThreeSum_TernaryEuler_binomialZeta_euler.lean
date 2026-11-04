-- Prove2me | solution 1 for ThreeSum.TernaryEuler.binomialZeta_euler
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:12:42.860191+00:00
-- url     : https://prove2.me/submissions/24b654bc-1a9a-42f1-a8ec-0c424526d397

import Definitions.Def_Submission_ThreeSum_TernaryQuery
import Definitions.Def_Submission_ThreeSum_TernaryEuler
import Theorems.Thm_ThreeSum_TernaryEuler_binomialZeta_euler_general
import Theorems.Thm_ThreeSum_TernaryBank_mem_bank
import Theorems.Thm_ThreeSum_TernaryBank_mem_lowerWords
import Theorems.Thm_ThreeSum_TernaryBank_mem_nearWords
attribute [local simp] ThreeSum.TernaryBank.mem_bank
attribute [local simp] ThreeSum.TernaryBank.mem_lowerWords
attribute [local simp] ThreeSum.TernaryBank.mem_nearWords



set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryEuler
open Finset
open ThreeSum.TernaryJointType ThreeSum.TernaryBank
namespace ThreeSum.TernaryEuler
theorem _root_.solution {N : ℕ} (f : TritWord N → ℤ) (h : ℕ)
    (hf : ∀ A, f A ≠ 0 → rank A = h) (R : TritWord N) :
    (∑ i : Fin N, (R i).val * binomialZeta f (predecessor R i)) =
      ((rank R : ℤ) - (h : ℤ)) * binomialZeta f R := by
  rw [binomialZeta_euler_general]
  unfold binomialZeta
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro A hA
  by_cases hzero : f A = 0
  · simp [hzero]
  · rw [hf A hzero]
    ring
end ThreeSum.TernaryEuler

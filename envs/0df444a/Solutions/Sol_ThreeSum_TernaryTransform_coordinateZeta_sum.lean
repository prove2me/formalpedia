-- Prove2me | solution 1 for ThreeSum.TernaryTransform.coordinateZeta_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:20:37.674938+00:00
-- url     : https://prove2.me/submissions/4b262929-b166-499d-882c-1b9279aa053a

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
theorem _root_.solution {N : ℕ} {α : Type*} [Fintype α]
    (i : Fin N) (H : α → TritWord N → ℤ) (R : TritWord N) :
    coordinateZeta i (fun Q => ∑ A, H A Q) R = ∑ A, coordinateZeta i (H A) R := by
  generalize hd : R i = d
  fin_cases d <;>
    simp [coordinateZeta, zetaDigit, hd, Fin.ext_iff,
      Finset.sum_add_distrib, Finset.mul_sum]
end ThreeSum.TernaryTransform

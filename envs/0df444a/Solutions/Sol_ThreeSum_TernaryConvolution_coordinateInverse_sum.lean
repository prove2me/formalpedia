-- Prove2me | solution 1 for ThreeSum.TernaryConvolution.coordinateInverse_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:23:42.194626+00:00
-- url     : https://prove2.me/submissions/94eb2632-36e2-42be-8cee-9a0ca1fb560c

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
theorem _root_.solution {N : ℕ} {α : Type*} [Fintype α]
    (i : Fin N) (H : α → TritWord N → ℤ) (Q : TritWord N) :
    coordinateInverse i (fun R => ∑ A, H A R) Q =
      ∑ A, coordinateInverse i (H A) Q := by
  generalize hd : Q i=d
  fin_cases d <;>
    simp [coordinateInverse,inverseDigit,hd,Fin.ext_iff,
      Finset.sum_sub_distrib,Finset.sum_add_distrib,Finset.mul_sum]
end ThreeSum.TernaryConvolution

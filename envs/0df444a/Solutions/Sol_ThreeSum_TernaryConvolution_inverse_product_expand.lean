-- Prove2me | solution 1 for ThreeSum.TernaryConvolution.inverse_product_expand
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:36:40.069087+00:00
-- url     : https://prove2.me/submissions/96cc2aeb-719e-499b-aee9-83255eebed17

import Definitions.Def_Submission_ThreeSum_TernaryReconstruction
import Definitions.Def_Submission_ThreeSum_TernaryTransform
import Mathlib.Algebra.BigOperators.Finprod
import Definitions.Def_Submission_ThreeSum_TernaryConvolution
import Theorems.Thm_ThreeSum_TernaryConvolution_coefficient_sum
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
theorem _root_.solution {N : ℕ} (f g : TritWord N → ℤ) (Q : TritWord N) :
    binomialInverse (fun R => binomialZeta f R * binomialZeta g R) Q =
      ∑ A, ∑ B, pairCoefficient Q A B * f A * g B := by
  unfold binomialInverse binomialZeta
  simp only [Finset.mul_sum,Finset.sum_mul]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro A hA
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro B hB
  calc
    (∑ R, inverseWeight Q R * (weight R B * f B * (weight R A * g A))) =
        (∑ R, inverseWeight Q R * weight R B * weight R A) * f B * g A := by
      rw [Finset.sum_mul,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro R hR
      ring
    _ = pairCoefficient Q B A * f B * g A := by rw [coefficient_sum]
end ThreeSum.TernaryConvolution

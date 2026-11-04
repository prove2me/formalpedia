-- Prove2me | solution 1 for ThreeSum.TernaryConvolution.factorial_convolution
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:40:20.477468+00:00
-- url     : https://prove2.me/submissions/50473a85-fea2-45b9-8d00-9e10184fc799

import Definitions.Def_Submission_ThreeSum_TernaryReconstruction
import Definitions.Def_Submission_ThreeSum_TernaryTransform
import Mathlib.Algebra.BigOperators.Finprod
import Definitions.Def_Submission_ThreeSum_TernaryConvolution
import Theorems.Thm_ThreeSum_TernaryConvolution_pairCoefficient_factorial
import Theorems.Thm_ThreeSum_TernaryConvolution_inverse_product_expand
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
theorem _root_.solution {N a b : ℕ} (f g : TritWord N → ℤ)
    (hf : ∀ A, f A≠0 → rank A=a) (hg : ∀ B, g B≠0 → rank B=b)
    (Q : TritWord N) (hQ : rank Q=a+b) :
    binomialInverse
      (fun R => binomialZeta (fun A => factorial A*f A) R *
        binomialZeta (fun B => factorial B*g B) R) Q =
      factorial Q * convolution f g Q := by
  rw [inverse_product_expand]
  unfold convolution
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro A hA
  apply Finset.sum_congr rfl
  intro B hB
  by_cases hzA : f A=0
  · simp [hzA]
  by_cases hzB : g B=0
  · simp [hzB]
  have hrank : rank A+rank B=rank Q := by rw [hf A hzA,hg B hzB,hQ]
  have hp := pairCoefficient_factorial Q A B hrank
  calc
    pairCoefficient Q A B * (factorial A*f A) * (factorial B*g B) =
      (pairCoefficient Q A B * factorial A * factorial B) * (f A*g B) := by ring
    _ = (if Adds A B Q then factorial Q else 0) * (f A*g B) := by rw [hp]
    _ = factorial Q * (if Adds A B Q then f A*g B else 0) := by
      split_ifs <;> ring
end ThreeSum.TernaryConvolution

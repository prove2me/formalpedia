-- Prove2me | solution 1 for ThreeSum.TernaryEuler.binomialZeta_euler_general
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:10:34.871699+00:00
-- url     : https://prove2.me/submissions/b4b3d21c-9b8c-49e2-9ad5-905223b42a3d

import Definitions.Def_Submission_ThreeSum_TernaryQuery
import Definitions.Def_Submission_ThreeSum_TernaryEuler
import Theorems.Thm_ThreeSum_TernaryEuler_weight_euler
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
theorem _root_.solution {N : ℕ} (f : TritWord N → ℤ) (R : TritWord N) :
    (∑ i : Fin N, (R i).val * binomialZeta f (predecessor R i)) =
      ∑ A : TritWord N, ((rank R : ℤ) - (rank A : ℤ)) * weight R A * f A := by
  unfold binomialZeta
  simp only [Finset.mul_sum, ← mul_assoc]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro A hA
  rw [← Finset.sum_mul, weight_euler]
end ThreeSum.TernaryEuler

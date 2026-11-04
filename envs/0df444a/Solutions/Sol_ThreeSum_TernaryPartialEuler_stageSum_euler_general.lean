-- Prove2me | solution 1 for ThreeSum.TernaryPartialEuler.stageSum_euler_general
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:41:43.066394+00:00
-- url     : https://prove2.me/submissions/8fe7316a-8ddf-4546-b986-a3dc014e8e83

import Definitions.Def_Submission_ThreeSum_TernaryTransform
import Definitions.Def_Submission_ThreeSum_TernaryPartialEuler
import Theorems.Thm_ThreeSum_TernaryPartialEuler_kernel_euler
import Theorems.Thm_ThreeSum_TernaryBank_mem_bank
import Theorems.Thm_ThreeSum_TernaryBank_mem_lowerWords
import Theorems.Thm_ThreeSum_TernaryBank_mem_nearWords
attribute [local simp] ThreeSum.TernaryBank.mem_bank
attribute [local simp] ThreeSum.TernaryBank.mem_lowerWords
attribute [local simp] ThreeSum.TernaryBank.mem_nearWords



set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryPartialEuler
open Finset ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.TernaryEuler ThreeSum.TernaryTransform
set_option maxHeartbeats 2000000
namespace ThreeSum.TernaryPartialEuler
theorem _root_.solution {N : ℕ} (S : Finset (Fin N))
    (f : TritWord N→ℤ) (R : TritWord N) :
    (∑ i∈S, (R i).val*stageSum S f (predecessor R i))=
      ∑ A : TritWord N, ((rank R : ℤ)-(rank A : ℤ))*kernel S R A*f A := by
  unfold stageSum
  simp only [Finset.mul_sum,←mul_assoc]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro A hA
  rw [←Finset.sum_mul,kernel_euler]
end ThreeSum.TernaryPartialEuler

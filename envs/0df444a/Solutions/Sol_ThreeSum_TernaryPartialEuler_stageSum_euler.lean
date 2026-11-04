-- Prove2me | solution 1 for ThreeSum.TernaryPartialEuler.stageSum_euler
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:42:41.596707+00:00
-- url     : https://prove2.me/submissions/a1e3933a-d91f-4b83-8c95-9573b132fa57

import Definitions.Def_Submission_ThreeSum_TernaryTransform
import Definitions.Def_Submission_ThreeSum_TernaryPartialEuler
import Theorems.Thm_ThreeSum_TernaryPartialEuler_stageSum_euler_general
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
theorem _root_.solution {N h : ℕ} (S : Finset (Fin N)) (f : TritWord N→ℤ)
    (hf : ∀ A, f A≠0 → rank A=h) (R : TritWord N) :
    (∑ i∈S, (R i).val*stageSum S f (predecessor R i))=
      ((rank R : ℤ)-(h : ℤ))*stageSum S f R := by
  rw [stageSum_euler_general]
  unfold stageSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro A hA
  by_cases hz : f A=0
  · simp [hz]
  · rw [hf A hz]
    ring
end ThreeSum.TernaryPartialEuler

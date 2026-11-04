-- Prove2me | solution 1 for ThreeSum.TernaryBank.rank_update_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:03:46.618309+00:00
-- url     : https://prove2.me/submissions/c5eaf18e-5fb2-4eec-9c8c-7ec024a51979

import Definitions.Def_Submission_ThreeSum_TernaryJointType
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_Submission_ThreeSum_TernaryBank
import Theorems.Thm_ThreeSum_TernaryBank_mem_bank
import Theorems.Thm_ThreeSum_TernaryBank_mem_lowerWords
import Theorems.Thm_ThreeSum_TernaryBank_mem_nearWords
attribute [local simp] ThreeSum.TernaryBank.mem_bank
attribute [local simp] ThreeSum.TernaryBank.mem_lowerWords
attribute [local simp] ThreeSum.TernaryBank.mem_nearWords

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryBank
open Finset
open ThreeSum.TernaryJointType
namespace ThreeSum.TernaryBank
theorem _root_.solution {N : ℕ} (R : TritWord N) (i : Fin N) (d : Fin 3) :
    rank (Function.update R i d) + (R i).val = rank R + d.val := by
  unfold rank
  rw [← Finset.add_sum_erase univ (fun j => (R j).val) (mem_univ i),
    ← Finset.add_sum_erase univ (fun j => (Function.update R i d j).val) (mem_univ i)]
  have hrest :
      (∑ j ∈ (univ : Finset (Fin N)).erase i, (Function.update R i d j).val) =
      ∑ j ∈ (univ : Finset (Fin N)).erase i, (R j).val := by
    apply Finset.sum_congr rfl
    intro j hj
    simp [Function.update_of_ne (mem_erase.mp hj).1]
  rw [hrest]
  simp only [Function.update_self]
  omega
end ThreeSum.TernaryBank

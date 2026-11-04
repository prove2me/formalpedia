-- Prove2me | solution 1 for ThreeSum.TernaryEuler.predecessor_rank_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:04:04.769899+00:00
-- url     : https://prove2.me/submissions/488bb5e8-83be-4f52-83e2-e9b37b0e99af

import Definitions.Def_Submission_ThreeSum_TernaryQuery
import Definitions.Def_Submission_ThreeSum_TernaryEuler
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
theorem _root_.solution {N : ℕ} (R : TritWord N) (i : Fin N)
    (hi : 0 < (R i).val) : rank (predecessor R i) < rank R := by
  unfold rank predecessor
  rw [← Finset.add_sum_erase univ (fun j => (R j).val) (mem_univ i),
    ← Finset.add_sum_erase univ
      (fun j => (Function.update R i (predDigit (R i)) j).val) (mem_univ i)]
  have hrest :
      (∑ j ∈ (univ : Finset (Fin N)).erase i,
        (Function.update R i (predDigit (R i)) j).val) =
      ∑ j ∈ (univ : Finset (Fin N)).erase i, (R j).val := by
    apply Finset.sum_congr rfl
    intro j hj
    simp [Function.update_of_ne (mem_erase.mp hj).1]
  rw [hrest]
  simp only [Function.update_self, predDigit]
  omega
end ThreeSum.TernaryEuler

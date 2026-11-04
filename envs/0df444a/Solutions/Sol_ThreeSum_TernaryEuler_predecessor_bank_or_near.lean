-- Prove2me | solution 1 for ThreeSum.TernaryEuler.predecessor_bank_or_near
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:08:25.344544+00:00
-- url     : https://prove2.me/submissions/5586b5ef-a2fc-41f8-92c8-b0a3f200e79c

import Definitions.Def_Submission_ThreeSum_TernaryQuery
import Definitions.Def_Submission_ThreeSum_TernaryEuler
import Theorems.Thm_ThreeSum_TernaryEuler_predecessor_below
import Theorems.Thm_ThreeSum_TernaryBank_mem_bank
import Theorems.Thm_ThreeSum_TernaryBank_mem_nearWords
import Theorems.Thm_ThreeSum_TernaryBank_rank_add_deficit
attribute [local simp] ThreeSum.TernaryBank.mem_bank
attribute [local simp] ThreeSum.TernaryBank.mem_nearWords



set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryEuler
open Finset
open ThreeSum.TernaryJointType ThreeSum.TernaryBank
namespace ThreeSum.TernaryEuler
theorem _root_.solution {N T : ℕ} {R Q : TritWord N}
    (hRQ : Below R Q) (i : Fin N) :
    predecessor R i ∈ bank N T ∨
      predecessor R i ∈ nearWords Q (rank Q - (T+1)) := by
  by_cases hlow : rank (predecessor R i) ≤ T
  · exact Or.inl (mem_bank.mpr hlow)
  · apply Or.inr
    apply mem_nearWords.mpr
    have hbelow : Below (predecessor R i) Q := fun j =>
      (predecessor_below R i j).trans (hRQ j)
    refine ⟨hbelow, ?_⟩
    have hsum := rank_add_deficit hbelow
    omega
end ThreeSum.TernaryEuler

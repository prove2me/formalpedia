-- Prove2me | solution 1 for ThreeSum.TernaryBank.below_bank_or_near
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:03:47.691052+00:00
-- url     : https://prove2.me/submissions/0daa0c01-856d-4df3-af6e-b33e52447a1a

import Definitions.Def_Submission_ThreeSum_TernaryJointType
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_Submission_ThreeSum_TernaryBank
import Theorems.Thm_ThreeSum_TernaryBank_mem_bank
import Theorems.Thm_ThreeSum_TernaryBank_mem_nearWords
import Theorems.Thm_ThreeSum_TernaryBank_rank_add_deficit
attribute [local simp] ThreeSum.TernaryBank.mem_bank
attribute [local simp] ThreeSum.TernaryBank.mem_nearWords

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryBank
open Finset
open ThreeSum.TernaryJointType
namespace ThreeSum.TernaryBank
theorem _root_.solution {N T : ℕ} {R Q : TritWord N} (hRQ : Below R Q) :
    R ∈ bank N T ∨ R ∈ nearWords Q (rank Q-(T+1)) := by
  by_cases hlow : rank R ≤ T
  · exact Or.inl (mem_bank.mpr hlow)
  · apply Or.inr
    apply mem_nearWords.mpr
    refine ⟨hRQ, ?_⟩
    have hsum := rank_add_deficit hRQ
    omega
end ThreeSum.TernaryBank

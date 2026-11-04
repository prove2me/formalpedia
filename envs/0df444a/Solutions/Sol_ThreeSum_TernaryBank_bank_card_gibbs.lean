-- Prove2me | solution 1 for ThreeSum.TernaryBank.bank_card_gibbs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:06:04.583831+00:00
-- url     : https://prove2.me/submissions/f7f7faaf-ae03-4ccb-8274-2694174d1abc

import Definitions.Def_Submission_ThreeSum_TernaryJointType
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_Submission_ThreeSum_TernaryBank
import Theorems.Thm_ThreeSum_TernaryBank_mem_bank
import Theorems.Thm_ThreeSum_TernaryBank_mem_lowerWords
import Theorems.Thm_ThreeSum_TernaryBank_mem_nearWords
import Theorems.Thm_ThreeSum_TernaryBank_rank_generating_sum
attribute [local simp] ThreeSum.TernaryBank.mem_bank
attribute [local simp] ThreeSum.TernaryBank.mem_lowerWords
attribute [local simp] ThreeSum.TernaryBank.mem_nearWords
noncomputable section
namespace ThreeSum.TernaryBank
open Finset
open ThreeSum.TernaryJointType
private theorem pow_antitone (y : ℝ) (hy : 0 ≤ y) (hy1 : y ≤ 1)
    {a b : ℕ} (hab : a ≤ b) : y ^ b ≤ y ^ a := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hab
  rw [pow_add]
  exact mul_le_of_le_one_right (pow_nonneg hy _) (pow_le_one₀ hy hy1)
end ThreeSum.TernaryBank
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryBank
open Finset
open ThreeSum.TernaryJointType
namespace ThreeSum.TernaryBank
theorem _root_.solution (N T : ℕ) (y : ℝ) (hy : 0 ≤ y) (hy1 : y ≤ 1) :
    (bank N T).card * y ^ T ≤ (1 + y + y ^ 2) ^ N := by
  calc
    (bank N T).card * y ^ T = ∑ R ∈ bank N T, y ^ T := by simp
    _ ≤ ∑ R ∈ bank N T, y ^ rank R := by
      apply Finset.sum_le_sum
      intro R hR
      exact pow_antitone y hy hy1 (mem_bank.mp hR)
    _ ≤ ∑ R : TritWord N, y ^ rank R := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (subset_univ _)
      intro R hR hnot
      exact pow_nonneg hy _
    _ = (1 + y + y ^ 2) ^ N := rank_generating_sum N y
end ThreeSum.TernaryBank

-- Prove2me | solution 1 for ThreeSum.TernaryBank.nearWords_card_gibbs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:06:06.951214+00:00
-- url     : https://prove2.me/submissions/5916e122-508e-464d-a953-ec81395a1185

import Definitions.Def_Submission_ThreeSum_TernaryJointType
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_Submission_ThreeSum_TernaryBank
import Theorems.Thm_ThreeSum_TernaryBank_mem_bank
import Theorems.Thm_ThreeSum_TernaryBank_mem_lowerWords
import Theorems.Thm_ThreeSum_TernaryBank_mem_nearWords
import Theorems.Thm_ThreeSum_TernaryBank_deficit_generating_sum
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
theorem _root_.solution {N : ℕ} (Q : TritWord N) (D : ℕ)
    (z : ℝ) (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    (nearWords Q D).card * z ^ D ≤
      ∏ i : Fin N, (if Q i = 0 then 1 else if Q i = 1 then 1 + z
        else 1 + z + z ^ 2) := by
  calc
    (nearWords Q D).card * z ^ D = ∑ R ∈ nearWords Q D, z ^ D := by simp
    _ ≤ ∑ R ∈ nearWords Q D, z ^ deficit Q R := by
      apply Finset.sum_le_sum
      intro R hR
      exact pow_antitone z hz hz1 (mem_nearWords.mp hR).2
    _ ≤ ∑ R ∈ lowerWords Q, z ^ deficit Q R := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
      intro R hR hnot
      exact pow_nonneg hz _
    _ = _ := deficit_generating_sum Q z
end ThreeSum.TernaryBank

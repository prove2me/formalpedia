-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.WeightedCache.bank_card_gibbs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T10:08:28.57948+00:00
-- url     : https://prove2.me/submissions/15c993eb-aeaf-434a-ae3c-5f4658d86845

import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Cache
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_WeightedCache_bank_generating_sum
namespace WeightedCache3SUMRefinement_e1ae71d
namespace WeightedCache
open Finset
private theorem pow_antitone (y : ℝ) (hy : 0 ≤ y) (hy1 : y ≤ 1)
    {a b : ℕ} (hab : a ≤ b) : y ^ b ≤ y ^ a := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hab
  rw [pow_add]
  exact mul_le_of_le_one_right (pow_nonneg hy _) (pow_le_one₀ hy hy1)
end WeightedCache
end WeightedCache3SUMRefinement_e1ae71d
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open WeightedCache3SUMRefinement_e1ae71d.WeightedCache
open Finset
namespace WeightedCache3SUMRefinement_e1ae71d.WeightedCache
theorem _root_.solution (N : ℕ) (c : Fin 3 → ℕ) (T : ℕ)
    (y : ℝ) (hy : 0 ≤ y) (hy1 : y ≤ 1) :
    (bank N c T).card * y ^ T ≤ (∑ d : Fin 3, y ^ c d) ^ N := by
  calc
    (bank N c T).card * y ^ T = ∑ R ∈ bank N c T, y ^ T := by simp
    _ ≤ ∑ R ∈ bank N c T, y ^ cost c R := by
      apply sum_le_sum
      intro R hR
      exact pow_antitone y hy hy1 (by simpa [bank] using hR)
    _ ≤ ∑ R : Word N, y ^ cost c R := by
      apply sum_le_sum_of_subset_of_nonneg (subset_univ _)
      intro R _ _
      exact pow_nonneg hy _
    _ = _ := bank_generating_sum N c y
end WeightedCache3SUMRefinement_e1ae71d.WeightedCache

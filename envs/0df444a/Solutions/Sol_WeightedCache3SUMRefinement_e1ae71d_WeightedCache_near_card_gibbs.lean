-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.WeightedCache.near_card_gibbs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T10:08:29.233186+00:00
-- url     : https://prove2.me/submissions/b8674cc9-1bd2-4e6f-8292-6725ca9b291c

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
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_WeightedCache_deficit_generating_sum
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
theorem _root_.solution {N : ℕ} (c : Fin 3 → ℕ) (Q : Word N) (D : ℕ)
    (z : ℝ) (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    (near c Q D).card * z ^ D ≤
      ∏ i : Fin N, ∑ r : Fin 3, digitWeight c z (Q i) r := by
  calc
    (near c Q D).card * z ^ D = ∑ R ∈ near c Q D, z ^ D := by simp
    _ ≤ ∑ R ∈ near c Q D, z ^ deficit c Q R := by
      apply sum_le_sum
      intro R hR
      exact pow_antitone z hz hz1
        (show Below R Q ∧ deficit c Q R ≤ D by simpa [near] using hR).2
    _ = ∑ R ∈ near c Q D, if Below R Q then z ^ deficit c Q R else 0 := by
      apply sum_congr rfl
      intro R hR
      have hh : Below R Q := (show Below R Q ∧ deficit c Q R ≤ D by simpa [near] using hR).1
      simp [hh]
    _ ≤ ∑ R : Word N, if Below R Q then z ^ deficit c Q R else 0 := by
      apply sum_le_sum_of_subset_of_nonneg (subset_univ _)
      intro R _ _
      split_ifs <;> positivity
    _ = _ := deficit_generating_sum c Q z
end WeightedCache3SUMRefinement_e1ae71d.WeightedCache

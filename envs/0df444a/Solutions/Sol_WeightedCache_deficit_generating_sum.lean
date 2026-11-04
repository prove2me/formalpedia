-- Prove2me | solution 1 for WeightedCache.deficit_generating_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T06:26:23.675205+00:00
-- url     : https://prove2.me/submissions/db377d18-8895-4af2-a52d-9eabd87d6ef2

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
import Definitions.Def_Submission_Weighted_Cache

set_option autoImplicit false
open WeightedCache
open Finset
namespace WeightedCache
theorem _root_.solution {N : ℕ} (c : Fin 3 → ℕ) (Q : Word N) (z : ℝ) :
    (∑ R : Word N, if Below R Q then z ^ deficit c Q R else 0) =
      ∏ i : Fin N, ∑ r : Fin 3, digitWeight c z (Q i) r := by
  rw [Fintype.prod_sum]
  apply sum_congr rfl
  intro R _
  by_cases h : Below R Q
  · simp only [h, ↓reduceIte]
    have hh : (∏ i : Fin N, digitWeight c z (Q i) (R i)) =
        ∏ i : Fin N, z ^ (c (Q i) - c (R i)) := by
      apply prod_congr rfl
      intro i _
      simp [digitWeight, h i]
    rw [hh]
    exact (prod_pow_eq_pow_sum univ _ _).symm
  · simp only [h, ↓reduceIte]
    obtain ⟨i, hi⟩ := not_forall.mp h
    symm
    exact prod_eq_zero (mem_univ i) (by simp [digitWeight, hi])
end WeightedCache

-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.WeightedCache.bank_generating_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T10:07:20.520543+00:00
-- url     : https://prove2.me/submissions/4233b868-2db7-4306-a37a-a1c6ee2bb6b8

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

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open WeightedCache3SUMRefinement_e1ae71d.WeightedCache
open Finset
namespace WeightedCache3SUMRefinement_e1ae71d.WeightedCache
theorem _root_.solution (N : ℕ) (c : Fin 3 → ℕ) (y : ℝ) :
    (∑ R : Word N, y ^ cost c R) = (∑ d : Fin 3, y ^ c d) ^ N := by
  rw [Fintype.sum_pow]
  apply sum_congr rfl
  intro R _
  exact (prod_pow_eq_pow_sum univ (fun i => c (R i)) y).symm
end WeightedCache3SUMRefinement_e1ae71d.WeightedCache

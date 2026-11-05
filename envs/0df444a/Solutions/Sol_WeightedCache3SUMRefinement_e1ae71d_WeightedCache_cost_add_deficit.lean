-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.WeightedCache.cost_add_deficit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T10:06:22.174549+00:00
-- url     : https://prove2.me/submissions/95abaee7-f4b1-4cfe-b859-5ba0d7b611b5

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
theorem _root_.solution {N : ℕ} {c : Fin 3 → ℕ} (hc : Monotone c)
    {R Q : Word N} (h : Below R Q) : cost c R + deficit c Q R = cost c Q := by
  unfold cost deficit
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro i _
  exact Nat.add_sub_of_le (hc (h i))
end WeightedCache3SUMRefinement_e1ae71d.WeightedCache

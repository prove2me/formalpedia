-- Prove2me | solution 1 for WeightedCache.cost_add_deficit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T06:25:38.64221+00:00
-- url     : https://prove2.me/submissions/a04a9d4a-2b6c-4ae2-a49b-cbb64a5ba68e

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
theorem _root_.solution {N : ℕ} {c : Fin 3 → ℕ} (hc : Monotone c)
    {R Q : Word N} (h : Below R Q) : cost c R + deficit c Q R = cost c Q := by
  unfold cost deficit
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro i _
  exact Nat.add_sub_of_le (hc (h i))
end WeightedCache

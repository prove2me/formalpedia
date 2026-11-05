-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.WeightedCache.concrete_cost_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T10:06:22.82267+00:00
-- url     : https://prove2.me/submissions/066eafd6-dab1-4ee8-97de-f15f39d5203c

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
theorem _root_.solution : Monotone (![0, 1369, 2740] : Fin 3 → ℕ) := by
  intro a b hab
  fin_cases a <;> fin_cases b <;> norm_num [Fin.le_def] at *
end WeightedCache3SUMRefinement_e1ae71d.WeightedCache

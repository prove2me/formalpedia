-- Prove2me | solution 1 for WeightedCache.concrete_cost_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T06:27:45.299211+00:00
-- url     : https://prove2.me/submissions/1d881877-3871-4a11-91b8-47dbbddb5ed4

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
theorem _root_.solution : Monotone (![0, 512, 1025] : Fin 3 → ℕ) := by
  intro a b hab
  fin_cases a <;> fin_cases b <;> norm_num [Fin.le_def] at *
end WeightedCache

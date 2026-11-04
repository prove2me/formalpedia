-- Prove2me | solution 1 for WeightedCache.predecessor_below
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T06:28:15.885635+00:00
-- url     : https://prove2.me/submissions/97e09b59-7c2c-48b7-8e88-c542e5859c3e

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
theorem _root_.solution {N : ℕ} (R : Word N) (i : Fin N) :
    Below (predecessor R i) R := by
  intro j
  by_cases hj : j = i
  · subst j
    change (Function.update R i ⟨(R i).val - 1, by omega⟩ i).val ≤ (R i).val
    simp
  · simp [predecessor, Function.update_of_ne hj]
end WeightedCache

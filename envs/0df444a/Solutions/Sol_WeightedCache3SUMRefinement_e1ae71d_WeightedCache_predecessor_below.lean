-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.WeightedCache.predecessor_below
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T10:07:16.316142+00:00
-- url     : https://prove2.me/submissions/aa82190a-fc9e-471e-ae4d-278cb8734c29

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
theorem _root_.solution {N : ℕ} (R : Word N) (i : Fin N) :
    Below (predecessor R i) R := by
  intro j
  by_cases hj : j = i
  · subst j
    change (Function.update R i ⟨(R i).val - 1, by omega⟩ i).val ≤ (R i).val
    simp
  · simp [predecessor, Function.update_of_ne hj]
end WeightedCache3SUMRefinement_e1ae71d.WeightedCache

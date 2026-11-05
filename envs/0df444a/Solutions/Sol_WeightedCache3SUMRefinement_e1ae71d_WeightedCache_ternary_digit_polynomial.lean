-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.WeightedCache.ternary_digit_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T10:07:14.731179+00:00
-- url     : https://prove2.me/submissions/28baaf95-6cfd-4219-9f43-0cb43030eb1b

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
theorem _root_.solution (a b : ℕ) (z : ℝ) (q : Fin 3) :
    (∑ r : Fin 3, digitWeight ![0, a, b] z q r) =
      if q = 0 then 1 else if q = 1 then 1 + z ^ a else
        1 + z ^ (b - a) + z ^ b := by
  fin_cases q <;> simp [digitWeight, Fin.sum_univ_succ, Fin.le_def] <;> ring
end WeightedCache3SUMRefinement_e1ae71d.WeightedCache

-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.WeightedCache.concrete_base_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T10:07:15.533204+00:00
-- url     : https://prove2.me/submissions/505bd81a-0ce5-489d-80f5-5ccba8e7cf31

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
theorem _root_.solution {N : ℕ} (R : Word N) :
    2 * cost ![0, 1369, 2740] R ≤ 2740 * rank R := by
  unfold cost rank
  rw [mul_sum, mul_sum]
  apply sum_le_sum
  intro i _
  generalize R i = d
  fin_cases d <;> norm_num
end WeightedCache3SUMRefinement_e1ae71d.WeightedCache

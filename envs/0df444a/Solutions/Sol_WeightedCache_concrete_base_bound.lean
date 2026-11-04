-- Prove2me | solution 1 for WeightedCache.concrete_base_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T06:27:46.23119+00:00
-- url     : https://prove2.me/submissions/3a843c2d-8808-4e13-83e7-d42c239aed39

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
theorem _root_.solution {N : ℕ} (R : Word N) :
    2 * cost ![0, 512, 1025] R ≤ 1025 * rank R := by
  unfold cost rank
  rw [mul_sum, mul_sum]
  apply sum_le_sum
  intro i _
  generalize R i = d
  fin_cases d <;> norm_num
end WeightedCache

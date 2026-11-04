-- Prove2me | solution 1 for WeightedCache.bank_generating_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T06:26:04.345521+00:00
-- url     : https://prove2.me/submissions/9cc11e0b-422b-48e0-8985-3f6c99395a44

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
theorem _root_.solution (N : ℕ) (c : Fin 3 → ℕ) (y : ℝ) :
    (∑ R : Word N, y ^ cost c R) = (∑ d : Fin 3, y ^ c d) ^ N := by
  rw [Fintype.sum_pow]
  apply sum_congr rfl
  intro R _
  exact (prod_pow_eq_pow_sum univ (fun i => c (R i)) y).symm
end WeightedCache

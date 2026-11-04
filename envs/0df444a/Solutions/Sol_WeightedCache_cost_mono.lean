-- Prove2me | solution 1 for WeightedCache.cost_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T06:25:37.252839+00:00
-- url     : https://prove2.me/submissions/1c0e11e5-6627-465d-a75e-7a81804ed1de

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
    {R Q : Word N} (h : Below R Q) : cost c R ≤ cost c Q :=
  sum_le_sum (fun i _ => hc (h i))
end WeightedCache

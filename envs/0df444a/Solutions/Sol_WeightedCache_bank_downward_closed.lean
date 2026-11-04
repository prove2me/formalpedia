-- Prove2me | solution 1 for WeightedCache.bank_downward_closed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T06:26:17.469761+00:00
-- url     : https://prove2.me/submissions/a442effc-3434-4dbe-8372-4db25fbf9652

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
import Theorems.Thm_WeightedCache_cost_mono

set_option autoImplicit false
open WeightedCache
open Finset
namespace WeightedCache
theorem _root_.solution {N T : ℕ} {c : Fin 3 → ℕ} (hc : Monotone c)
    {R Q : Word N} (h : Below R Q) (hQ : Q ∈ bank N c T) : R ∈ bank N c T := by
  simp only [bank, mem_filter, mem_univ, true_and] at hQ ⊢
  exact (cost_mono hc h).trans hQ
end WeightedCache

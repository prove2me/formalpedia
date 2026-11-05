-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.WeightedCache.weighted_bank_contains_base
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T10:07:27.030406+00:00
-- url     : https://prove2.me/submissions/2169ae7f-a092-44b6-be31-e07dc89b4b95

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
theorem _root_.solution {N h T C : ℕ} (c : Fin 3 → ℕ)
    (hc : ∀ d, c d ≤ C * d.val) (hcut : C * h ≤ T)
    (R : Word N) (hR : rank R ≤ h) : R ∈ bank N c T := by
  have hh : cost c R ≤ C * rank R := by
    unfold cost rank
    rw [mul_sum]
    exact sum_le_sum (fun i _ => hc (R i))
  simpa [bank] using hh.trans ((Nat.mul_le_mul_left C hR).trans hcut)
end WeightedCache3SUMRefinement_e1ae71d.WeightedCache

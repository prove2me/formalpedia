-- Prove2me | solution 1 for WeightedCache.weighted_bank_contains_base
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T06:27:44.35008+00:00
-- url     : https://prove2.me/submissions/96b2e8a8-308a-448f-a041-704f9f7e2654

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
theorem _root_.solution {N h T C : ℕ} (c : Fin 3 → ℕ)
    (hc : ∀ d, c d ≤ C * d.val) (hcut : C * h ≤ T)
    (R : Word N) (hR : rank R ≤ h) : R ∈ bank N c T := by
  have hh : cost c R ≤ C * rank R := by
    unfold cost rank
    rw [mul_sum]
    exact sum_le_sum (fun i _ => hc (R i))
  simpa [bank] using hh.trans ((Nat.mul_le_mul_left C hR).trans hcut)
end WeightedCache

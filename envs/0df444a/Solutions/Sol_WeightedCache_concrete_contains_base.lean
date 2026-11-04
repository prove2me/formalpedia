-- Prove2me | solution 1 for WeightedCache.concrete_contains_base
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T06:28:14.773323+00:00
-- url     : https://prove2.me/submissions/40d701ea-59bc-4d79-8722-1421742bbdf0

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
import Theorems.Thm_WeightedCache_concrete_base_bound

set_option autoImplicit false
open WeightedCache
open Finset
namespace WeightedCache
theorem _root_.solution {N h T : ℕ} (hcut : 1025 * h ≤ 2 * T)
    (R : Word N) (hR : rank R ≤ h) : R ∈ bank N ![0, 512, 1025] T := by
  have hc := concrete_base_bound R
  have hr := Nat.mul_le_mul_left 1025 hR
  simp only [bank, mem_filter, mem_univ, true_and]
  omega
end WeightedCache

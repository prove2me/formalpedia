-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.WeightedCache.concrete_contains_base
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T10:08:34.929753+00:00
-- url     : https://prove2.me/submissions/95b3dcaa-6536-4ee2-aea4-1ec82d8868d7

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
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_WeightedCache_concrete_base_bound

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open WeightedCache3SUMRefinement_e1ae71d.WeightedCache
open Finset
namespace WeightedCache3SUMRefinement_e1ae71d.WeightedCache
theorem _root_.solution {N h T : ℕ} (hcut : 2740 * h ≤ 2 * T)
    (R : Word N) (hR : rank R ≤ h) : R ∈ bank N ![0, 1369, 2740] T := by
  have hc := concrete_base_bound R
  have hr := Nat.mul_le_mul_left 2740 hR
  simp only [bank, mem_filter, mem_univ, true_and]
  omega
end WeightedCache3SUMRefinement_e1ae71d.WeightedCache

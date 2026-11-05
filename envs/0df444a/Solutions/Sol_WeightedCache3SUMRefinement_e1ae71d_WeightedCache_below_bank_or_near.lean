-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.WeightedCache.below_bank_or_near
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T10:07:14.040192+00:00
-- url     : https://prove2.me/submissions/f5270644-31d3-4cf7-9a26-99d5cb35985b

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
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_WeightedCache_cost_add_deficit

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open WeightedCache3SUMRefinement_e1ae71d.WeightedCache
open Finset
namespace WeightedCache3SUMRefinement_e1ae71d.WeightedCache
theorem _root_.solution {N T : ℕ} {c : Fin 3 → ℕ} (hc : Monotone c)
    {R Q : Word N} (h : Below R Q) :
    R ∈ bank N c T ∨ R ∈ near c Q (cost c Q - (T + 1)) := by
  by_cases hlow : cost c R ≤ T
  · exact Or.inl (by simpa [bank] using hlow)
  · apply Or.inr
    have hh := cost_add_deficit hc h
    simpa only [near, mem_filter, mem_univ, true_and] using
      (show Below R Q ∧ deficit c Q R ≤ cost c Q - (T + 1) from ⟨h, by omega⟩)
end WeightedCache3SUMRefinement_e1ae71d.WeightedCache

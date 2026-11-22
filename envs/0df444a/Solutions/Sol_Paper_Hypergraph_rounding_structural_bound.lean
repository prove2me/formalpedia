-- Prove2me | solution 1 for Paper.Hypergraph.rounding_structural_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:12:06.376625+00:00
-- url     : https://prove2.me/submissions/8fcf6811-0e65-4703-81f9-8fd9e04f42da

import Definitions.Def_Paper_TrustBoundary
import Definitions.Def_Paper_Formalized

set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper
open Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (d a : ℕ) :
    min (8 + 4 * Real.log (a : ℝ)) (6 * (d : ℝ)) + 1 ≤
      9 * (1 + min (d : ℝ) (Real.log (2 + (a : ℝ)))) := by
  have ha : 0 ≤ (a : ℝ) := Nat.cast_nonneg _
  have hl : 0 ≤ Real.log (2 + (a : ℝ)) := Real.log_nonneg (by linarith)
  have hal : Real.log (a : ℝ) ≤ Real.log (2 + (a : ℝ)) := by
    by_cases h : a = 0
    · simpa [h] using hl
    · exact Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero h) (by linarith)
  rcases le_total (d : ℝ) (Real.log (2 + (a : ℝ))) with h | h
  · rw [min_eq_left h]
    have := min_le_right (8 + 4 * Real.log (a : ℝ)) (6 * (d : ℝ))
    have : 0 ≤ (d : ℝ) := Nat.cast_nonneg _
    linarith [min_le_right (8 + 4 * Real.log (a : ℝ)) (6 * (d : ℝ))]
  · rw [min_eq_right h]
    linarith [min_le_left (8 + 4 * Real.log (a : ℝ)) (6 * (d : ℝ))]
end Paper.Hypergraph

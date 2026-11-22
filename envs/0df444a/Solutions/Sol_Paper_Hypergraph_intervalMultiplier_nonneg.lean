-- Prove2me | solution 1 for Paper.Hypergraph.intervalMultiplier_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:03:39.352718+00:00
-- url     : https://prove2.me/submissions/3adac094-c00f-4261-8f08-4ba385efef9b

import Definitions.Def_Paper_TwoTerminalRounding
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Definitions.Def_Paper_RoundingAveraging
import Theorems.Thm_Paper_Hypergraph_vertexMultiplier_nonneg

set_option autoImplicit true
noncomputable section
open scoped BigOperators
open MeasureTheory Set
open Paper Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution {V : Finset ℕ} (hne : V.Nonempty) {x d : ℕ → ℝ}
    (hx : ∀ v ∈ V, 0 ≤ x v) (r : ℝ) : 0 ≤ intervalMultiplier V hne x d r := by
  obtain ⟨v, hv⟩ := hne
  unfold intervalMultiplier
  exact (vertexMultiplier_nonneg (d := d) (hx v hv) r).trans
    (Finset.le_sup' (fun w => vertexMultiplier x d w r) hv)
end Paper.Hypergraph

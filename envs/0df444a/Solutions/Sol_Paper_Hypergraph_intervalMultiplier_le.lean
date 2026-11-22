-- Prove2me | solution 1 for Paper.Hypergraph.intervalMultiplier_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:03:42.321329+00:00
-- url     : https://prove2.me/submissions/8f1fc04c-205b-4dc8-b84b-90d0394d4f7a

import Definitions.Def_Paper_TwoTerminalRounding
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Definitions.Def_Paper_RoundingAveraging

set_option autoImplicit true
noncomputable section
open scoped BigOperators
open MeasureTheory Set
open Paper Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution {V : Finset ℕ} (hne : V.Nonempty) {x d : ℕ → ℝ} {ε : ℝ}
    (hε : 0 < ε) (hx : ∀ v ∈ V, x v = 0 ∨ ε ≤ x v) (r : ℝ) :
    intervalMultiplier V hne x d r ≤ 1 / ε := by
  apply Finset.sup'_le
  intro v hv
  rcases hx v hv with h0 | hpos
  · simp [vertexMultiplier, h0]
    positivity
  · by_cases hr : r ∈ Icc (d v - x v) (d v)
    · simpa [vertexMultiplier, hr] using one_div_le_one_div_of_le hε hpos
    · simp [vertexMultiplier, hr, le_of_lt hε]
end Paper.Hypergraph

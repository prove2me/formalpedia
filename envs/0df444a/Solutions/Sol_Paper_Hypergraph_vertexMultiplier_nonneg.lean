-- Prove2me | solution 1 for Paper.Hypergraph.vertexMultiplier_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:55:38.289516+00:00
-- url     : https://prove2.me/submissions/dee3cd5d-946b-48a7-91f4-546c8375977d

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
theorem _root_.solution {x d : ℕ → ℝ} {v : ℕ} (hx : 0 ≤ x v) (r : ℝ) :
    0 ≤ vertexMultiplier x d v r := by
  exact Set.indicator_nonneg (fun _ _ => div_nonneg zero_le_one hx) r
end Paper.Hypergraph

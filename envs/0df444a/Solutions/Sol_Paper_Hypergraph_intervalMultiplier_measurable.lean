-- Prove2me | solution 1 for Paper.Hypergraph.intervalMultiplier_measurable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:18:12.355426+00:00
-- url     : https://prove2.me/submissions/53837f00-07d3-475b-b7f5-b8bbba9a788d

import Definitions.Def_Paper_TwoTerminalRounding
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Definitions.Def_Paper_RoundingAveraging
import Theorems.Thm_Paper_Hypergraph_vertexMultiplier_measurable

set_option autoImplicit true
noncomputable section
open scoped BigOperators
open MeasureTheory Set
open Paper Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (V : Finset ℕ) (hne : V.Nonempty) (x d : ℕ → ℝ) :
    Measurable (intervalMultiplier V hne x d) := by
  convert Finset.measurable_sup' hne (fun v _ => vertexMultiplier_measurable x d v) using 1
  funext r
  simp [intervalMultiplier, Finset.sup'_apply]
end Paper.Hypergraph

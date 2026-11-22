-- Prove2me | solution 1 for Paper.Hypergraph.vertexMultiplier_measurable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:17:25.191384+00:00
-- url     : https://prove2.me/submissions/3475313f-d6aa-4aaa-8e8f-98f1ed58d4a1

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
theorem _root_.solution (x d : ℕ → ℝ) (v : ℕ) :
    Measurable (vertexMultiplier x d v) := measurable_const.indicator measurableSet_Icc
end Paper.Hypergraph

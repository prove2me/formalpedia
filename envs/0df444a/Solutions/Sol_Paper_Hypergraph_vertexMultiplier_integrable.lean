-- Prove2me | solution 1 for Paper.Hypergraph.vertexMultiplier_integrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:04:30.976821+00:00
-- url     : https://prove2.me/submissions/d2d6d050-3eba-42c0-b057-a23fc9ec60a0

import Definitions.Def_Paper_RoundingAveraging
import Definitions.Def_Paper_RoundingDegeneracy

set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset MeasureTheory
attribute [local instance] Classical.propDecidable
open Paper Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (x d : ℕ → ℝ) (v : ℕ) :
    Integrable (vertexMultiplier x d v) levelMeasure :=
  (integrable_const _).indicator measurableSet_Icc
end Paper.Hypergraph

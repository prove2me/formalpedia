-- Prove2me | solution 1 for QEC.Coding.BDL26RXXStarTransport.gradient_potential_nonzero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T14:29:48.792475+00:00
-- url     : https://prove2.me/submissions/697ae25a-bdee-45e3-95ff-751bc302b6fe

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXXStarTransport_Geometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXXStarTransport
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_gradient_potential_boundary_nonzero

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXXStarTransport
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RXDecoderAdapter BDL26RXErrorPullback
open BDL26RZMap1CoordinateBridge MultiscaleDecoder RXCoarseGraining
open RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (h : i.val % 2=0)
namespace QEC.Coding.BDL26RXXStarTransport
theorem _root_.solution (x : XCoord S i) (a : Upper S depth i) :
    potential S depth i h x a (a+gradientError S depth i h x) ≠ 0 := by
  intro hz
  apply gradient_potential_boundary_nonzero S depth i h x a
  rw [hz,map_zero]
end QEC.Coding.BDL26RXXStarTransport

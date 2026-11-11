-- Prove2me | solution 1 for QEC.Coding.BDL26RXXStarTransport.potential_boundary_x
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T14:02:15.61202+00:00
-- url     : https://prove2.me/submissions/83e03b16-6bc2-4375-9472-01f916576cb8

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXXStarTransport_Geometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXXStarTransport
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_localPotential_boundary
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans


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
theorem _root_.solution (x : XCoord S i) (a b : Upper S depth i) :
    restrictWordLinear ((rxLx S depth i h).correctionRegion x)
      ((indexedFamily S depth).coboundary0 i.succ (potential S depth i h x a b)) =
      restrictWordLinear ((rxLx S depth i h).correctionRegion x) (updated S depth i h a b) :=
  ((rxContract S depth i h).support_decomposition.cxDelta0_restriction x _).trans
    (localPotential_boundary S depth i h x a b)
end QEC.Coding.BDL26RXXStarTransport

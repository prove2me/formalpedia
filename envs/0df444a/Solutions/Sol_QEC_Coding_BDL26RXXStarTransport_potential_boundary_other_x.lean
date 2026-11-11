-- Prove2me | solution 1 for QEC.Coding.BDL26RXXStarTransport.potential_boundary_other_x
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T13:14:04.071337+00:00
-- url     : https://prove2.me/submissions/41c93a8d-c78c-43b1-9dbc-f0c5655d4763

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXXStarTransport_Geometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXXStarTransport
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_rxXLift_boundary_other_x


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
theorem _root_.solution (x y : XCoord S i) (hy : y≠x) (a b : Upper S depth i) :
    restrictWordLinear ((rxLx S depth i h).correctionRegion y)
      ((indexedFamily S depth).coboundary0 i.succ (potential S depth i h x a b))=0 :=
  rxXLift_boundary_other_x S depth i h x y hy _
end QEC.Coding.BDL26RXXStarTransport

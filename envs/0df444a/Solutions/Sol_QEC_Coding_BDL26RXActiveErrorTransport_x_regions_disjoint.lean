-- Prove2me | solution 1 for QEC.Coding.BDL26RXActiveErrorTransport.x_regions_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T13:37:12.735234+00:00
-- url     : https://prove2.me/submissions/a37635c5-52e0-4e06-9d2f-3ffa3d738d75

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXFiniteBlockTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXActiveErrorTransport

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXActiveErrorTransport
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RXDecoderAdapter BDL26RXErrorPullback
open BDL26RZMap1CoordinateBridge BDL26RXXStarTransport MultiscaleDecoder RXCoarseGraining
open RXCoarseGraining.RXCoarseGrainingData
open BDL26BoundedValence BDL26GraphQuantitativeBounds
open scoped BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (h : i.val % 2=0)
namespace QEC.Coding.BDL26RXActiveErrorTransport
theorem _root_.solution (x y : XCoord S i) (hn : x≠y) :
    Disjoint ((rxLx S depth i h).correctionRegion x) ((rxLx S depth i h).correctionRegion y) :=
  (rxData S depth i h).cx_correction_regions_pairwise_disjoint x y hn
end QEC.Coding.BDL26RXActiveErrorTransport

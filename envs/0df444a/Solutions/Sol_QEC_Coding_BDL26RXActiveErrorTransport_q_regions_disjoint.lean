-- Prove2me | solution 1 for QEC.Coding.BDL26RXActiveErrorTransport.q_regions_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T13:37:16.638595+00:00
-- url     : https://prove2.me/submissions/2886302c-e9c8-4f6d-b96e-feeedf248a96

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
theorem _root_.solution (q r : QCoord S i) (hn : q≠r) :
    Disjoint ((rxLq S depth i h).correctionRegion q) ((rxLq S depth i h).correctionRegion r) :=
  (rxData S depth i h).cq_correction_regions_pairwise_disjoint q r hn
end QEC.Coding.BDL26RXActiveErrorTransport

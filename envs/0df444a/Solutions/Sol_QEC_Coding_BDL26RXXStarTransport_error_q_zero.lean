-- Prove2me | solution 1 for QEC.Coding.BDL26RXXStarTransport.error_q_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T23:19:50.303063+00:00
-- url     : https://prove2.me/submissions/e8082a42-7725-427d-bd7c-d7ae8e329fdc

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXQBlockTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXXStarTransport_Geometry
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_zero_off_support
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_x_q_disjoint

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
theorem _root_.solution (x : XCoord S i) (e : Upper S depth i)
    (he : hammingSupport e ⊆ (rxLx S depth i h).correctionRegion x)
    (q : QCoord S i) : restrictWordLinear ((rxLq S depth i h).correctionRegion q) e=0 := by
  funext p
  exact zero_off_support e _ he p.val
    (fun hp => (Finset.disjoint_left.mp (x_q_disjoint S depth i h x q)) hp p.property)
end QEC.Coding.BDL26RXXStarTransport

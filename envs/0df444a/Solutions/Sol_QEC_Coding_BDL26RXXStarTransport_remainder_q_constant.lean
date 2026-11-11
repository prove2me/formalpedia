-- Prove2me | solution 1 for QEC.Coding.BDL26RXXStarTransport.remainder_q_constant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T14:42:15.241745+00:00
-- url     : https://prove2.me/submissions/d8de452d-4772-4f67-8acd-e67e29953d2c

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXXStarTransport_Geometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXXStarTransport
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_remainder_q_kernel
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_rxQ_kernel_constant


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
theorem _root_.solution (x : XCoord S i) (q : QCoord S i) (a b : Upper S depth i)
    (he : OneX S depth i h x a b)
    (v : QDoubleCylinderVertex (state S i.val).presentation q S) :
    remainder S depth i h x a b (rxQVertexEquiv S depth i h q v).val =
      lowerWord S depth i h x a b q :=
  rxQ_kernel_constant S depth i h q _ (remainder_q_kernel S depth i h x q a b he) v
end QEC.Coding.BDL26RXXStarTransport

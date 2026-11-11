-- Prove2me | solution 1 for QEC.Coding.BDL26RXFiniteBlockTransport.remainder_q_constant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T16:29:18.49162+00:00
-- url     : https://prove2.me/submissions/63d396bc-a20c-4ce6-8646-fd3bde4338c6

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXXStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXFiniteBlockTransport
import Theorems.Thm_QEC_Coding_BDL26RXFiniteBlockTransport_remainder_q_kernel
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_rxQ_kernel_constant
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_remainder_q_kernel


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXFiniteBlockTransport
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RXDecoderAdapter BDL26RXErrorPullback
open BDL26RZMap1CoordinateBridge BDL26RXXStarTransport MultiscaleDecoder RXCoarseGraining
open RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (h : i.val % 2=0)
namespace QEC.Coding.BDL26RXFiniteBlockTransport
theorem _root_.solution (X0 : Finset (XCoord S i)) (Q0 : Finset (QCoord S i))
    (q : QCoord S i) (a b : Upper S depth i) (he : Localized S depth i h X0 Q0 a b)
    (v : QDoubleCylinderVertex (state S i.val).presentation q S) :
    R S depth i h X0 a b (rxQVertexEquiv S depth i h q v).val = L S depth i h X0 a b q :=
  rxQ_kernel_constant S depth i h q _ (remainder_q_kernel S depth i h X0 Q0 q a b he) v
end QEC.Coding.BDL26RXFiniteBlockTransport

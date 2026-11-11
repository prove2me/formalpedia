-- Prove2me | solution 1 for QEC.Coding.BDL26RXFiniteBlockTransport.gradient_pair_canonical_cx_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T14:11:12.330025+00:00
-- url     : https://prove2.me/submissions/e3c6e88b-2a17-4031-87f8-5b46980b4b26

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXXStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXFiniteBlockTransport
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_gradient_canonical_cx_eq
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans


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
theorem _root_.solution (x0 x1 y : XCoord S i) (a : Upper S depth i) :
    cxComponentTotal (rxData S depth i h) (errorSyndrome S depth i a).val y =
      cxComponentTotal (rxData S depth i h)
        (errorSyndrome S depth i (a+(gradientError S depth i h x0+gradientError S depth i h x1))).val y := by
  rw [← add_assoc]
  exact (gradient_canonical_cx_eq S depth i h x0 y a).trans
    (gradient_canonical_cx_eq S depth i h x1 y (a+gradientError S depth i h x0))
end QEC.Coding.BDL26RXFiniteBlockTransport

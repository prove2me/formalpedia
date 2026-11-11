-- Prove2me | solution 1 for QEC.Coding.BDL26RXPhysicalStarTransport.boundaryCenter_gradient_restriction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T16:32:57.454745+00:00
-- url     : https://prove2.me/submissions/3b17b035-2367-4c9c-80b3-7cd049e5a9ee

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXFiniteBlockTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXPhysicalStarTransport
import Theorems.Thm_QEC_Coding_BDL26RXPhysicalStarTransport_boundaryCenter_basis

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXPhysicalStarTransport
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RXDecoderAdapter BDL26RXErrorPullback
open BDL26RZMap1CoordinateBridge BDL26RXXStarTransport
open BDL26RXLocalReplacement BDL26ReplacementSupport MultiscaleDecoder
open RXCoarseGraining RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (h : i.val % 2=0)
namespace QEC.Coding.BDL26RXPhysicalStarTransport
theorem _root_.solution (x : XCoord S i) :
    restrictWordLinear ((rxLx S depth i h).correctionRegion x)
      (gradient S depth i (boundaryCenter S depth i h x))=boundaryGradient S depth i h x := by
  rw [gradient,boundaryCenter_basis]
  exact (rxContract S depth i h).support_decomposition.cxDelta0_restriction x _
end QEC.Coding.BDL26RXPhysicalStarTransport

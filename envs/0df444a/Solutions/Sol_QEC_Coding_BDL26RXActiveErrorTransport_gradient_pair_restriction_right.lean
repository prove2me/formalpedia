-- Prove2me | solution 1 for QEC.Coding.BDL26RXActiveErrorTransport.gradient_pair_restriction_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T10:52:07.794061+00:00
-- url     : https://prove2.me/submissions/c39d3009-0d46-4326-a8a2-93b3b7a164f6

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXFiniteBlockTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXActiveErrorTransport
import Theorems.Thm_QEC_Coding_BDL26RXActiveErrorTransport_gradient_pair_restriction_left
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


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
theorem _root_.solution (x0 x1 : XCoord S i) (hn : x0≠x1) :
    restrictWordLinear ((rxLx S depth i h).correctionRegion x1)
      (gradientError S depth i h x0+gradientError S depth i h x1)=boundaryGradient S depth i h x1 := by
  rw [add_comm (gradientError S depth i h x0) (gradientError S depth i h x1)]
  exact gradient_pair_restriction_left S depth i h x1 x0 hn.symm
end QEC.Coding.BDL26RXActiveErrorTransport

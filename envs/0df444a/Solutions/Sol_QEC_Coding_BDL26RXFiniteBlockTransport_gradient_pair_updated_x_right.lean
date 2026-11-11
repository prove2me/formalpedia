-- Prove2me | solution 1 for QEC.Coding.BDL26RXFiniteBlockTransport.gradient_pair_updated_x_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T16:15:07.619391+00:00
-- url     : https://prove2.me/submissions/430081d2-bf22-4b52-b238-f87002aa4fde

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXXStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXFiniteBlockTransport
import Theorems.Thm_QEC_Coding_BDL26RXFiniteBlockTransport_gradient_pair_updated_x_left
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


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
theorem _root_.solution (x0 x1 : XCoord S i) (hne : x0≠x1)
    (a : Upper S depth i) :
    restrictWordLinear ((rxLx S depth i h).correctionRegion x1)
      (updated S depth i h a (a+(gradientError S depth i h x0+gradientError S depth i h x1))) =
      boundaryGradient S depth i h x1 := by
  rw [add_comm (gradientError S depth i h x0) (gradientError S depth i h x1)]
  exact gradient_pair_updated_x_left S depth i h x1 x0 hne.symm a
end QEC.Coding.BDL26RXFiniteBlockTransport

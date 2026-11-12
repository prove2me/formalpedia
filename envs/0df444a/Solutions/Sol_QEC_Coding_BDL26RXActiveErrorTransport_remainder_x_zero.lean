-- Prove2me | solution 1 for QEC.Coding.BDL26RXActiveErrorTransport.remainder_x_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T03:16:45.828933+00:00
-- url     : https://prove2.me/submissions/63007a14-c058-4f3f-bad2-3367892c3035

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXFiniteBlockTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXActiveErrorTransport
import Theorems.Thm_QEC_Coding_BDL26RXActiveErrorTransport_localized
import Theorems.Thm_QEC_Coding_BDL26RXFiniteBlockTransport_remainder_x_zero
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_remainder_x_zero


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
theorem _root_.solution (a b : Upper S depth i) (x : XCoord S i) :
    restrictWordLinear ((rxLx S depth i h).correctionRegion x) (R S depth i h a b)=0 :=
  BDL26RXFiniteBlockTransport.remainder_x_zero S depth i h _ _ x a b (localized S depth i h a b)
end QEC.Coding.BDL26RXActiveErrorTransport

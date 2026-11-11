-- Prove2me | solution 1 for QEC.Coding.BDL26RXActiveErrorTransport.remainder_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T14:00:20.696927+00:00
-- url     : https://prove2.me/submissions/6920486c-3c40-4a4f-aafa-6936b65c8149

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXFiniteBlockTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXActiveErrorTransport
import Theorems.Thm_QEC_Coding_BDL26RXFiniteBlockTransport_remainder_self
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_remainder_self
attribute [local simp] QEC.Coding.BDL26RXFiniteBlockTransport.remainder_self
attribute [local simp] QEC.Coding.BDL26RXXStarTransport.remainder_self



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
theorem _root_.solution (a : Upper S depth i) : R S depth i h a a=0 :=
  BDL26RXFiniteBlockTransport.remainder_self S depth i h _ a
end QEC.Coding.BDL26RXActiveErrorTransport

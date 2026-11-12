-- Prove2me | solution 1 for QEC.Coding.BDL26RXActiveErrorTransport.map1_eq_remainder
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T03:15:02.659843+00:00
-- url     : https://prove2.me/submissions/f8554a40-2abb-4349-b71e-7d9f579f74c6

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXFiniteBlockTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXActiveErrorTransport
import Theorems.Thm_QEC_Coding_BDL26RXActiveErrorTransport_localized
import Theorems.Thm_QEC_Coding_BDL26RXFiniteBlockTransport_map1_eq_remainder
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_map1_eq_remainder


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
theorem _root_.solution (a b : Upper S depth i) :
    ((indexedDecoderData S depth).selectedMap i).map1 (L S depth i h a b)=R S depth i h a b :=
  BDL26RXFiniteBlockTransport.map1_eq_remainder S depth i h _ _ a b (localized S depth i h a b)
end QEC.Coding.BDL26RXActiveErrorTransport

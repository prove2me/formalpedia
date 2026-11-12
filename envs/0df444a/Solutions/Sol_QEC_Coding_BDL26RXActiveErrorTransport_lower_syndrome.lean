-- Prove2me | solution 1 for QEC.Coding.BDL26RXActiveErrorTransport.lower_syndrome
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T11:04:15.001376+00:00
-- url     : https://prove2.me/submissions/d6540ddf-d492-451f-b19e-9070443793e8

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXFiniteBlockTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXActiveErrorTransport
import Theorems.Thm_QEC_Coding_BDL26RXActiveErrorTransport_localized
import Theorems.Thm_QEC_Coding_BDL26RXFiniteBlockTransport_lower_syndrome
import Theorems.Thm_QEC_Coding_BDL26RXQBlockTransport_lower_syndrome
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_lower_syndrome


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
    (indexedFamily S depth).coboundary1 i.castSucc (L S depth i h a b)=(coarseSum S depth i h a b).val :=
  BDL26RXFiniteBlockTransport.lower_syndrome S depth i h _ _ a b (localized S depth i h a b)
end QEC.Coding.BDL26RXActiveErrorTransport

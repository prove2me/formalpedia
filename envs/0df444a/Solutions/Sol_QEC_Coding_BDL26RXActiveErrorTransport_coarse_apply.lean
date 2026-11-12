-- Prove2me | solution 1 for QEC.Coding.BDL26RXActiveErrorTransport.coarse_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T03:16:59.936279+00:00
-- url     : https://prove2.me/submissions/8410535d-16d6-4a7f-9e34-69f1087a9719

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXFiniteBlockTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXActiveErrorTransport
import Theorems.Thm_QEC_Coding_BDL26RXActiveErrorTransport_localized
import Theorems.Thm_QEC_Coding_BDL26RXFiniteBlockTransport_coarse_apply
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_coarse_apply


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
theorem _root_.solution (a b : Upper S depth i) (z : ZCoord S i) :
    (coarseSum S depth i h a b).val z = ∑ q ∈ N S depth i h a b, L S depth i h a b q *
      (if (state S i.val).presentation.qz q z=true then 1 else 0) :=
  BDL26RXFiniteBlockTransport.coarse_apply S depth i h _ _ a b (localized S depth i h a b) z
end QEC.Coding.BDL26RXActiveErrorTransport

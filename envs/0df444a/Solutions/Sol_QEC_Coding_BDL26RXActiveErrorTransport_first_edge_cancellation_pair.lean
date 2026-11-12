-- Prove2me | solution 1 for QEC.Coding.BDL26RXActiveErrorTransport.first_edge_cancellation_pair
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T03:20:21.750968+00:00
-- url     : https://prove2.me/submissions/618389b0-d3bd-4c8e-b0f7-667154a66138

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXFiniteBlockTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXActiveErrorTransport
import Theorems.Thm_QEC_Coding_BDL26RXFiniteBlockTransport_first_edge_cancellation_pair


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
open BDL26FiniteAlternatingCore
namespace QEC.Coding.BDL26RXActiveErrorTransport
theorem _root_.solution (S : OddScale) (depth : Nat) (hd : 0<depth)
    (a : Upper S depth ⟨0,hd⟩) (copy : Fin 2) :
    let i : StepIndex depth := ⟨0,hd⟩
    let b := a+((indexedDecoderData S depth).selectedMap i).map1 BDL26RXFiniteBlockTransport.seedWord
    ((indexedDecoderData S depth).selectedMap i).map2 (coarseSum S depth i (by rfl) a b).val
        ((rxData S depth i (by rfl)).induced.zPairEquiv ((0 : BaseZ),copy)).val=0 ∧
      ((indexedDecoderData S depth).selectedMap i).map2 (coarseSum S depth i (by rfl) a b).val
        ((rxData S depth i (by rfl)).induced.zPairEquiv ((1 : BaseZ),copy)).val=1 :=
  BDL26RXFiniteBlockTransport.first_edge_cancellation_pair S depth hd a copy
end QEC.Coding.BDL26RXActiveErrorTransport

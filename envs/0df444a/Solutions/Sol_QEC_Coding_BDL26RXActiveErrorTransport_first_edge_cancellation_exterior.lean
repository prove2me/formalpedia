-- Prove2me | solution 1 for QEC.Coding.BDL26RXActiveErrorTransport.first_edge_cancellation_exterior
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T03:20:59.231706+00:00
-- url     : https://prove2.me/submissions/0df022e6-5e43-4247-9967-be2c5f5da260

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXFiniteBlockTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXActiveErrorTransport
import Theorems.Thm_QEC_Coding_BDL26RXFiniteBlockTransport_first_edge_cancellation_exterior


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
    (a : Upper S depth ⟨0,hd⟩) (p : FamilyZ S depth (⟨0,hd⟩ : StepIndex depth).succ)
    (hp : p ∉ (rxData S depth ⟨0,hd⟩ (by rfl)).zSector) :
    let i : StepIndex depth := ⟨0,hd⟩
    let b := a+((indexedDecoderData S depth).selectedMap i).map1 BDL26RXFiniteBlockTransport.seedWord
    ((indexedDecoderData S depth).selectedMap i).map2 (coarseSum S depth i (by rfl) a b).val p=0 :=
  BDL26RXFiniteBlockTransport.first_edge_cancellation_exterior S depth hd a p hp
end QEC.Coding.BDL26RXActiveErrorTransport

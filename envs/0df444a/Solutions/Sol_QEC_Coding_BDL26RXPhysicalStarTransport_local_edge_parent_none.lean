-- Prove2me | solution 1 for QEC.Coding.BDL26RXPhysicalStarTransport.local_edge_parent_none
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T14:11:46.42156+00:00
-- url     : https://prove2.me/submissions/112b9b54-09a1-48f9-92fd-9d0473aeaa0d

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXFiniteBlockTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXPhysicalStarTransport
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_rxPhysical_localEdge_parent_none


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
theorem _root_.solution (x : XCoord S i)
    (e : DoubleCylinderEdge (state S i.val).presentation x S) :
    parent S (i.val+1) (Vertex.q (upperQChart S depth i h (Sum.inl ⟨x,e⟩)))=none := by
  exact rxPhysical_localEdge_parent_none S depth i h x e
end QEC.Coding.BDL26RXPhysicalStarTransport

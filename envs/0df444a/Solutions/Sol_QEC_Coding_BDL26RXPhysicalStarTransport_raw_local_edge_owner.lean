-- Prove2me | solution 1 for QEC.Coding.BDL26RXPhysicalStarTransport.raw_local_edge_owner
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T13:19:11.02165+00:00
-- url     : https://prove2.me/submissions/d0cd100c-c760-4cb9-9b37-74fd130a43d2

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXFiniteBlockTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXPhysicalStarTransport
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXPhysicalStarTransport
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RXDecoderAdapter BDL26RXErrorPullback
open BDL26RZMap1CoordinateBridge BDL26RXXStarTransport
open BDL26RXLocalReplacement BDL26ReplacementSupport MultiscaleDecoder
open RXCoarseGraining RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
namespace QEC.Coding.BDL26RXPhysicalStarTransport
theorem _root_.solution (P : TannerSquarePresentation) (S : OddScale)
    (u : RX0 P S) (e : Σ x : P.X, DoubleCylinderEdge P x S)
    (hu : rxXQIncidence P S u (Sum.inl e)=true) : u.1=e.1 := by
  obtain ⟨f,c,hf,hq⟩ := (rxXQIncidence_eq_true_iff P S u (Sum.inl e)).mp hu
  obtain ⟨endpoint,he⟩ := rxFaceX_eq_endpoint_of_faceQ_eq_xEdge P S f c e.1 e.2 hq
  have hh := congrArg Sigma.fst (hf.symm.trans he)
  exact hh
end QEC.Coding.BDL26RXPhysicalStarTransport

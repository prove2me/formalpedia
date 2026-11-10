-- Prove2me | solution 1 for QEC.Coding.BDL26RXDecoderAdapter.rxQ_kernel_constant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T05:02:39.711058+00:00
-- url     : https://prove2.me/submissions/c5b583eb-727b-4c74-8361-27f31f1c6ad9

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Decomposition
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Coordinates
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Flow
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Lifts
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Representative
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Graph
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Sectors
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Induced
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Budgets
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_LocalComplexes
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_IndexedDecoder
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_localCq_delta1_apply
import Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_word_eq_root_of_graphCoboundary_eq_zero
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm

section
namespace QEC.Coding.BDL26RXDecoderAdapter
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementSupport BDL26ReplacementCochainMaps BDL26RXStagedRestriction
open BDL26DecodingGraph BDL26AlternatingCochain MultiscaleDecoder RXCoarseGraining
open BDL26RZMap1CoordinateBridge (tannerCoboundary0 tannerCoboundary1)
open scoped Classical BigOperators
open BDL26IndexedDecoder BDL26AlternatingCochain
variable (S : OddScale) (depth : Nat) (i : StepIndex depth)
open RXCoarseGrainingData
private theorem actualEndpoint_qKernel (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P) (S : OddScale) :
    EndpointQKernel (actualEndpoint P A R S) (qCorrectionEquiv P S) := by
  intro q w hw v
  let raw : Word BDL26Field (QDoubleCylinderVertex P q S) :=
    fun t => w (qCorrectionEquiv P S q t)
  have hz : wordLinearMapTranspose (qDoubleCylinderBoundary1 P q S) raw = 0 := by
    funext e
    have he := congrFun hw (qSyndromeEquiv P S q e)
    change wordLinearMapTranspose (localCq P S q).boundary2 w
      (qSyndromeEquiv P S q e) = 0 at he
    exact (localCq_delta1_apply P S q w e).symm.trans he
  exact word_eq_root_of_graphCoboundary_eq_zero
    (qDoubleCylinderEdgeStart P q S) (qDoubleCylinderEdgeEnd P q S)
    (0, Sum.inl (Sum.inl ())) (qDoubleCylinderPath P A.toTannerSquareAdmissible q S)
    raw hz v
private theorem transportQKernel (P U V : TannerSquarePresentation) (S : OddScale)
    (h : U = V) (G : EndpointData P V S) (E : EndpointQCoordinates G)
    (hk : EndpointQKernel G E) :
    EndpointQKernel (transportEndpoint P U V S h G)
      (transportQCoordinates P U V S h G E) := by
  cases h
  exact hk
end QEC.Coding.BDL26RXDecoderAdapter
noncomputable section
namespace QEC.Coding.BDL26RXDecoderAdapter
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementSupport BDL26ReplacementCochainMaps BDL26RXStagedRestriction
open BDL26DecodingGraph BDL26AlternatingCochain MultiscaleDecoder RXCoarseGraining
open BDL26RZMap1CoordinateBridge (tannerCoboundary0 tannerCoboundary1)
open scoped Classical BigOperators
open RXCoarseGrainingData
end QEC.Coding.BDL26RXDecoderAdapter
end
namespace QEC.Coding.BDL26RXDecoderAdapter
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity MultiscaleDecoder
open RXCoarseGraining RXCoarseGrainingData
end QEC.Coding.BDL26RXDecoderAdapter
noncomputable section
namespace QEC.Coding.BDL26RXDecoderAdapter
open BDL26IndexedDecoder
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementSupport BDL26ReplacementCochainMaps BDL26RXStagedRestriction
open BDL26DecodingGraph BDL26AlternatingCochain MultiscaleDecoder RXCoarseGraining
open BDL26RZMap1CoordinateBridge (tannerCoboundary0 tannerCoboundary1)
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (h : i.val % 2 = 0)
end QEC.Coding.BDL26RXDecoderAdapter
noncomputable section
namespace QEC.Coding.BDL26RXDecoderAdapter
open BDL26IndexedDecoder BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26ReplacementSupport BDL26DecodingGraph
open MultiscaleDecoder
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (h : i.val % 2 = 0)
end QEC.Coding.BDL26RXDecoderAdapter
noncomputable section
namespace QEC.Coding.BDL26RXDecoderAdapter
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26DecodingGraph BDL26IndexedDecoder MultiscaleDecoder
open scoped Classical
end QEC.Coding.BDL26RXDecoderAdapter
end
end
end
end

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXDecoderAdapter
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementSupport BDL26ReplacementCochainMaps BDL26RXStagedRestriction
open BDL26DecodingGraph BDL26AlternatingCochain MultiscaleDecoder RXCoarseGraining
open BDL26RZMap1CoordinateBridge (tannerCoboundary0 tannerCoboundary1)
open scoped Classical BigOperators
open BDL26IndexedDecoder BDL26AlternatingCochain
variable (S : OddScale) (depth : Nat) (i : StepIndex depth)
open RXCoarseGrainingData
namespace QEC.Coding.BDL26RXDecoderAdapter
theorem _root_.solution (h : i.val % 2 = 0)
    (q : (state S i.val).presentation.Q)
    (w : Word BDL26Field (LocalRegionIndex ((rxLq S depth i h).correctionRegion q)))
    (hw : (rxContract S depth i h).rx_local_complexes.cqDelta1 q w = 0)
    (v : QDoubleCylinderVertex (state S i.val).presentation q S) :
    w (rxQVertexEquiv S depth i h q v) =
      w (rxQVertexEquiv S depth i h q (0, Sum.inl (Sum.inl ()))) := by
  have hk := transportQKernel _ _ _ S
    (congrArg ConstructionState.presentation (stateSuccRX S depth i h))
    (actualEndpoint (state S i.val).presentation (state S i.val).admissible
      (state S i.val).regular S)
    (qCorrectionEquiv (state S i.val).presentation S)
    (actualEndpoint_qKernel (state S i.val).presentation (state S i.val).admissible
      (state S i.val).regular S)
  exact hk q w hw v
end QEC.Coding.BDL26RXDecoderAdapter

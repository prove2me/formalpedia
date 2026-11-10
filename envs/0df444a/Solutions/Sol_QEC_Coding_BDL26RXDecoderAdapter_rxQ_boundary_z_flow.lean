-- Prove2me | solution 1 for QEC.Coding.BDL26RXDecoderAdapter.rxQ_boundary_z_flow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T05:22:40.440213+00:00
-- url     : https://prove2.me/submissions/f3678a14-cc56-44be-b57e-56ed7f7eb55a

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
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans

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
private theorem actualEndpoint_qBoundaryFlow (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P) (S : OddScale) :
    EndpointQBoundaryFlow (actualEndpoint P A R S) := by
  intro q f z b
  let G := actualEndpoint P A R S
  have hp : (G.pairEquiv (z,b)).val ∉ G.lq.syndromeRegion q := by
    change Sum.inr (z,b) ∉ (localQ P S).syndromeRegion q
    intro hm
    have hh := (Finset.mem_filter.mp hm).2
    cases hh
  have he : extendWordLinear (G.lq.syndromeRegion q)
      (wordLinearMapTranspose (G.cq q).boundary2 f) (G.pairEquiv (z,b)).val = 0 := by
    exact dif_neg hp
  rw [G.qDecomposition]
  exact (congrArg (fun t => t + G.qFlow q f (G.pairEquiv (z,b)).val) he).trans (zero_add _)
private theorem transportQBoundaryFlow (P U V : TannerSquarePresentation) (S : OddScale)
    (h : U = V) (G : EndpointData P V S) (hz : EndpointQBoundaryFlow G) :
    EndpointQBoundaryFlow (transportEndpoint P U V S h G) := by
  cases h
  exact hz
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
    (f : Word BDL26Field (LocalRegionIndex ((rxLq S depth i h).correctionRegion q)))
    (z : (state S i.val).presentation.Z) (b : Fin 2) :
    (indexedFamily S depth).coboundary1 i.succ
      (extendWordLinear ((rxLq S depth i h).correctionRegion q) f)
      ((rxData S depth i h).induced.zPairEquiv (z,b)).val =
    (rxContract S depth i h).support_decomposition.cqFlow q f
      ((rxData S depth i h).induced.zPairEquiv (z,b)).val := by
  have hz := transportQBoundaryFlow _ _ _ S
    (congrArg ConstructionState.presentation (stateSuccRX S depth i h))
    (actualEndpoint (state S i.val).presentation (state S i.val).admissible
      (state S i.val).regular S)
    (actualEndpoint_qBoundaryFlow (state S i.val).presentation
      (state S i.val).admissible (state S i.val).regular S)
  rw [indexedFamily_coboundary1]
  exact hz q f z b
end QEC.Coding.BDL26RXDecoderAdapter

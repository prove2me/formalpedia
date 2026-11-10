-- Prove2me | solution 1 for QEC.Coding.BDL26RXDecoderAdapter.rxMap1_constant_Q
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T05:03:04.317814+00:00
-- url     : https://prove2.me/submissions/9c830bfd-ffb0-45e8-a32c-1ea1d4e34977

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
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_map1_representative_decomposition
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_qRepresentative_value
attribute [local simp] QEC.Coding.BDL26RXDecoderAdapter.qRepresentative_value


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
private theorem actualEndpoint_constantMap1 (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P) (S : OddScale) :
    EndpointConstantMap1 (actualEndpoint P A R S) := by
  intro c
  change rxMap1Coord P S c = ∑ q, extendWordLinear ((localQ P S).correctionRegion q) (fun _ => c q)
  rw [map1_representative_decomposition P A.toTannerSquareAdmissible S]
  apply Finset.sum_congr rfl
  intro q _
  congr 1
  funext p
  exact qRepresentative_value P A.toTannerSquareAdmissible S q c p
private theorem transportConstantMap1 (P U V : TannerSquarePresentation) (S : OddScale)
    (h : U = V) (G : EndpointData P V S) (hc : EndpointConstantMap1 G) :
    EndpointConstantMap1 (transportEndpoint P U V S h G) := by
  cases h
  exact hc
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
    (c : Word BDL26Field (state S i.val).presentation.Q) :
    ((indexedDecoderData S depth).rxMap i).map1 c =
      ∑ q, extendWordLinear ((rxLq S depth i h).correctionRegion q) (fun _ => c q) := by
  have hc := transportConstantMap1 _ _ _ S
    (congrArg ConstructionState.presentation (stateSuccRX S depth i h))
    (actualEndpoint (state S i.val).presentation (state S i.val).admissible
      (state S i.val).regular S)
    (actualEndpoint_constantMap1 (state S i.val).presentation (state S i.val).admissible
      (state S i.val).regular S)
  change (indexedEdgeMap S depth i).map1 c = _
  rw [← (endpointAt_maps S depth i h).2.1]
  exact hc c
end QEC.Coding.BDL26RXDecoderAdapter

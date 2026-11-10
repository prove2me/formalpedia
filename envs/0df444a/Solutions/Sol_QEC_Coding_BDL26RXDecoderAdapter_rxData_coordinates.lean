-- Prove2me | solution 1 for QEC.Coding.BDL26RXDecoderAdapter.rxData_coordinates
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T05:04:25.613865+00:00
-- url     : https://prove2.me/submissions/51a1bdab-2940-4ad5-92c2-b9e09a5147b4

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
private theorem transportEndpoint_regions (P U V : TannerSquarePresentation) (S : OddScale)
    (h : U = V) (G : EndpointData P V S) :
    HEq (transportEndpoint P U V S h G).lx.syndromeRegion G.lx.syndromeRegion ∧
    HEq (transportEndpoint P U V S h G).lx.correctionRegion G.lx.correctionRegion ∧
    HEq (transportEndpoint P U V S h G).lq.syndromeRegion G.lq.syndromeRegion ∧
    HEq (transportEndpoint P U V S h G).lq.correctionRegion G.lq.correctionRegion ∧
    HEq (transportEndpoint P U V S h G).lz.syndromeRegion G.lz.syndromeRegion ∧
    HEq (transportEndpoint P U V S h G).lz.correctionRegion G.lz.correctionRegion ∧
    HEq (transportEndpoint P U V S h G).topCenter G.topCenter ∧
    HEq (transportEndpoint P U V S h G).correctionOwner G.correctionOwner := by
  cases h
  exact ⟨HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl⟩
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
theorem _root_.solution (h : i.val % 2 = 0) :
    HEq (rxLx S depth i h).syndromeRegion (localX (state S i.val).presentation S).syndromeRegion ∧
    HEq (rxLx S depth i h).correctionRegion (localX (state S i.val).presentation S).correctionRegion ∧
    HEq (rxLq S depth i h).syndromeRegion (localQ (state S i.val).presentation S).syndromeRegion ∧
    HEq (rxLq S depth i h).correctionRegion (localQ (state S i.val).presentation S).correctionRegion ∧
    HEq (rxLz S depth i h).syndromeRegion (localZ (state S i.val).presentation S).syndromeRegion ∧
    HEq (rxLz S depth i h).correctionRegion (localZ (state S i.val).presentation S).correctionRegion ∧
    HEq (rxData S depth i h).topCenter (topCenter (state S i.val).presentation S) ∧
    HEq (correctionOwnerAt S depth i h)
      (fun p => (vertexEquiv (state S i.val).presentation).symm
        (rxCorrectionOwner (state S i.val).presentation S p)) := by
  exact transportEndpoint_regions _ _ _ S
    (congrArg ConstructionState.presentation (stateSuccRX S depth i h))
    (actualEndpoint (state S i.val).presentation (state S i.val).admissible
      (state S i.val).regular S)
end QEC.Coding.BDL26RXDecoderAdapter

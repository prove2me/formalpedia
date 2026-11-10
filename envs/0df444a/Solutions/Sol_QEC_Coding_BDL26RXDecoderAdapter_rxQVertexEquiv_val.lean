-- Prove2me | solution 1 for QEC.Coding.BDL26RXDecoderAdapter.rxQVertexEquiv_val
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T05:22:29.834324+00:00
-- url     : https://prove2.me/submissions/cfb9b9f7-20e2-4659-b1e0-aa3d4c2ce52d

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
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_qCorrectionEquiv_val
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm
attribute [local simp] QEC.Coding.BDL26RXDecoderAdapter.qCorrectionEquiv_val


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
private theorem transportQCoordinates_val
    (P U V : TannerSquarePresentation) (S : OddScale) (hp : U = V)
    (hq : V.Q = U.Q) (G : EndpointData P V S) (E : EndpointQCoordinates G)
    (q : P.Q) (v : QDoubleCylinderVertex P q S) :
    ((transportQCoordinates P U V S hp G E q) v).val =
      (Equiv.cast hq) (E q v).val := by
  cases hp
  rfl
end QEC.Coding.BDL26RXDecoderAdapter
end
end
end
end

set_option autoImplicit false
noncomputable section
noncomputable section
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXDecoderAdapter
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26DecodingGraph BDL26IndexedDecoder MultiscaleDecoder
open scoped Classical
namespace QEC.Coding.BDL26RXDecoderAdapter
theorem _root_.solution (S : OddScale) (depth : Nat) (i : StepIndex depth)
    (h : i.val % 2 = 0) (q : (state S i.val).presentation.Q)
    (v : QDoubleCylinderVertex (state S i.val).presentation q S) :
    (rxQVertexEquiv S depth i h q v).val =
      rxPhysicalQEquiv S depth i h (.inr ⟨q,v⟩) := by
  calc
    (rxQVertexEquiv S depth i h q v).val =
        rxPhysicalQEquiv S depth i h
          (qCorrectionEquiv (state S i.val).presentation S q v).val :=
      transportQCoordinates_val (state S i.val).presentation
        (state S (i.val+1)).presentation
        (rxReplacementPresentation (state S i.val).presentation S) S
        (congrArg ConstructionState.presentation (stateSuccRX S depth i h))
        (congrArg (fun C : ConstructionState => C.presentation.Q)
          (stateSuccRX S depth i h)).symm
        (actualEndpoint (state S i.val).presentation (state S i.val).admissible
          (state S i.val).regular S)
        (qCorrectionEquiv (state S i.val).presentation S) q v
    _ = rxPhysicalQEquiv S depth i h (.inr ⟨q,v⟩) :=
      congrArg (rxPhysicalQEquiv S depth i h)
        (qCorrectionEquiv_val (state S i.val).presentation S q v)
end QEC.Coding.BDL26RXDecoderAdapter

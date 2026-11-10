-- Prove2me | solution 1 for QEC.Coding.BDL26RXDecoderAdapter.rxPhysical_incidence
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T05:08:28.419585+00:00
-- url     : https://prove2.me/submissions/be1c8d06-3a7e-49c0-9f63-2b04e45edfa6

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
private theorem transportXCoordinates_xq
    (P U V : TannerSquarePresentation) (S : OddScale) (hp : U = V)
    (hq : V.Q = U.Q) (G : EndpointData P V S)
    (E : EndpointXCoordinates G)
    (r : Σ x : P.X, DoubleCylinderVertex P x S) (q : V.Q) :
    U.xq ((transportXCoordinates P U V S hp G E) r) ((Equiv.cast hq) q) =
      V.xq (E r) q := by
  cases hp
  rfl
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
noncomputable section
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXDecoderAdapter
open BDL26IndexedDecoder BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26ReplacementSupport BDL26DecodingGraph
open MultiscaleDecoder
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (h : i.val % 2 = 0)
namespace QEC.Coding.BDL26RXDecoderAdapter
theorem _root_.solution (r : RX0 (state S i.val).presentation S)
    (p : RX1 (state S i.val).presentation S) :
    (state S (i.val+1)).presentation.xq (rxDegreeZeroEquiv S depth i h r)
      (rxPhysicalQEquiv S depth i h p) = rxXQIncidence (state S i.val).presentation S r p := by
  unfold rxPhysicalQEquiv rxDegreeZeroEquiv
  erw [transportXCoordinates_xq]
  rfl
end QEC.Coding.BDL26RXDecoderAdapter

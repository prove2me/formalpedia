-- Prove2me | solution 1 for QEC.Coding.BDL26RXDecoderAdapter.xExtend_other
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T02:21:02.700459+00:00
-- url     : https://prove2.me/submissions/fa8cb3b9-be3f-4b57-9f71-0e28848b7ad2

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Coordinates
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Flow

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXDecoderAdapter
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementSupport BDL26ReplacementCochainMaps BDL26RXStagedRestriction
open BDL26DecodingGraph MultiscaleDecoder
open scoped Classical BigOperators
namespace QEC.Coding.BDL26RXDecoderAdapter
theorem _root_.solution (P : TannerSquarePresentation) (S : OddScale) (x y : P.X)
    (h : y ≠ x) (w : Word BDL26Field (DoubleCylinderEdge P x S))
    (e : DoubleCylinderEdge P y S) : xExtend P S x w (Sum.inl ⟨y,e⟩) = 0 := by
  change extendLocalSignal ((localX P S).correctionRegion x) _ (Sum.inl ⟨y,e⟩) = 0
  rw [extendLocalSignal, dif_neg]
  intro hp
  exact h (Vertex.x.inj (Finset.mem_filter.mp hp).2)
end QEC.Coding.BDL26RXDecoderAdapter

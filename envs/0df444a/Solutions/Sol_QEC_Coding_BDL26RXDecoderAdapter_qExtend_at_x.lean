-- Prove2me | solution 1 for QEC.Coding.BDL26RXDecoderAdapter.qExtend_at_x
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T02:47:08.331895+00:00
-- url     : https://prove2.me/submissions/0e6242e9-f4f0-4c4f-a553-ca1aac37c5dc

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Coordinates
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Flow

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXDecoderAdapter
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementSupport BDL26ReplacementCochainMaps BDL26RXStagedRestriction
open BDL26DecodingGraph MultiscaleDecoder
open scoped Classical BigOperators
namespace QEC.Coding.BDL26RXDecoderAdapter
theorem _root_.solution (P : TannerSquarePresentation) (S : OddScale) (q : P.Q)
    (w : Word BDL26Field (QDoubleCylinderVertex P q S)) (x : P.X)
    (e : DoubleCylinderEdge P x S) : qExtend P S q w (Sum.inl ⟨x,e⟩) = 0 := by
  change extendLocalSignal ((localQ P S).correctionRegion q) _ (Sum.inl ⟨x,e⟩) = 0
  rw [extendLocalSignal, dif_neg]
  intro hp
  have h := (Finset.mem_filter.mp hp).2
  cases h
end QEC.Coding.BDL26RXDecoderAdapter

-- Prove2me | solution 1 for QEC.Coding.BDL26RXDecoderAdapter.qExtend_other
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T02:47:20.273394+00:00
-- url     : https://prove2.me/submissions/abd1dd2c-b4ea-4358-adb1-3c27633a1f97

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Coordinates
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Flow

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXDecoderAdapter
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementSupport BDL26ReplacementCochainMaps BDL26RXStagedRestriction
open BDL26DecodingGraph MultiscaleDecoder
open scoped Classical BigOperators
namespace QEC.Coding.BDL26RXDecoderAdapter
theorem _root_.solution (P : TannerSquarePresentation) (S : OddScale) (q r : P.Q)
    (h : r ≠ q) (w : Word BDL26Field (QDoubleCylinderVertex P q S))
    (v : QDoubleCylinderVertex P r S) : qExtend P S q w (Sum.inr ⟨r,v⟩) = 0 := by
  change extendLocalSignal ((localQ P S).correctionRegion q) _ (Sum.inr ⟨r,v⟩) = 0
  rw [extendLocalSignal, dif_neg]
  intro hp
  exact h (Vertex.q.inj (Finset.mem_filter.mp hp).2)
end QEC.Coding.BDL26RXDecoderAdapter

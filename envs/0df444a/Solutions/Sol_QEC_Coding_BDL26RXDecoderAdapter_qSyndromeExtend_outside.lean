-- Prove2me | solution 1 for QEC.Coding.BDL26RXDecoderAdapter.qSyndromeExtend_outside
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T04:34:58.695184+00:00
-- url     : https://prove2.me/submissions/ec779c77-d120-43dc-be83-f4cffdc97821

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Flow
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Decomposition

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXDecoderAdapter
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementSupport BDL26ReplacementCochainMaps BDL26RXStagedRestriction
open MultiscaleDecoder
open scoped Classical BigOperators
namespace QEC.Coding.BDL26RXDecoderAdapter
theorem _root_.solution (P : TannerSquarePresentation) (S : OddScale) (q : P.Q)
    (w : Word BDL26Field (QDoubleCylinderEdge P q S)) (p : RX2 P S)
    (hp : rxSyndromeOwner P S p ≠ Vertex.q q) : qSyndromeExtend P S q w p = 0 := by
  change extendLocalSignal ((localQ P S).syndromeRegion q) _ p = 0
  rw [extendLocalSignal, dif_neg]
  intro hm
  exact hp (Finset.mem_filter.mp hm).2
end QEC.Coding.BDL26RXDecoderAdapter

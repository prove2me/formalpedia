-- Prove2me | solution 1 for QEC.Coding.BDL26RXDecoderAdapter.xSyndromeExtend_outside
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T04:34:23.618198+00:00
-- url     : https://prove2.me/submissions/e6c97fb0-2524-41aa-83d3-1d2bd83eb70f

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Flow
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Decomposition

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXDecoderAdapter
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementSupport BDL26ReplacementCochainMaps BDL26RXStagedRestriction
open MultiscaleDecoder
open scoped Classical BigOperators
namespace QEC.Coding.BDL26RXDecoderAdapter
theorem _root_.solution (P : TannerSquarePresentation) (S : OddScale) (x : P.X)
    (w : Word BDL26Field (DoubleCylinderFace P x S)) (p : RX2 P S)
    (hp : rxSyndromeOwner P S p ≠ Vertex.x x) : xSyndromeExtend P S x w p = 0 := by
  change extendLocalSignal ((localX P S).syndromeRegion x) _ p = 0
  rw [extendLocalSignal, dif_neg]
  intro hm
  exact hp (Finset.mem_filter.mp hm).2
end QEC.Coding.BDL26RXDecoderAdapter

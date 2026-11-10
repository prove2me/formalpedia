-- Prove2me | solution 1 for QEC.Coding.BDL26RXDecoderAdapter.xExtend_at_x
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T02:47:02.642177+00:00
-- url     : https://prove2.me/submissions/e3c4a54d-201f-49e5-bc14-a2527e92fdb5

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Coordinates
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Flow
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_extend_reindex_at

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXDecoderAdapter
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementSupport BDL26ReplacementCochainMaps BDL26RXStagedRestriction
open BDL26DecodingGraph MultiscaleDecoder
open scoped Classical BigOperators
namespace QEC.Coding.BDL26RXDecoderAdapter
theorem _root_.solution (P : TannerSquarePresentation) (S : OddScale) (x : P.X)
    (w : Word BDL26Field (DoubleCylinderEdge P x S)) (a : DoubleCylinderEdge P x S) :
    xExtend P S x w (Sum.inl ⟨x,a⟩) = w a :=
  extend_reindex_at _ (xCorrectionEquiv P S x) w a
end QEC.Coding.BDL26RXDecoderAdapter

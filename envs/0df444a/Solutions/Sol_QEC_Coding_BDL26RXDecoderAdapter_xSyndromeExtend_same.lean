-- Prove2me | solution 1 for QEC.Coding.BDL26RXDecoderAdapter.xSyndromeExtend_same
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T04:32:24.900382+00:00
-- url     : https://prove2.me/submissions/1b7bbb38-74ea-429a-b106-13834a8352e5

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Flow
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Decomposition
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_extend_reindex_at


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXDecoderAdapter
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementSupport BDL26ReplacementCochainMaps BDL26RXStagedRestriction
open MultiscaleDecoder
open scoped Classical BigOperators
namespace QEC.Coding.BDL26RXDecoderAdapter
theorem _root_.solution (P : TannerSquarePresentation) (S : OddScale) (x : P.X)
    (w : Word BDL26Field (DoubleCylinderFace P x S)) (f : DoubleCylinderFace P x S) :
    xSyndromeExtend P S x w (Sum.inl (Sum.inl ⟨x,f⟩)) = w f :=
  extend_reindex_at _ (xSyndromeEquiv P S x) w f
end QEC.Coding.BDL26RXDecoderAdapter

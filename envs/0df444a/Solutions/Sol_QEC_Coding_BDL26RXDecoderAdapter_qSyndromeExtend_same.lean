-- Prove2me | solution 1 for QEC.Coding.BDL26RXDecoderAdapter.qSyndromeExtend_same
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T04:34:02.850149+00:00
-- url     : https://prove2.me/submissions/c2290e33-6b74-404c-911e-dadc3a537a7b

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
theorem _root_.solution (P : TannerSquarePresentation) (S : OddScale) (q : P.Q)
    (w : Word BDL26Field (QDoubleCylinderEdge P q S)) (e : QDoubleCylinderEdge P q S) :
    qSyndromeExtend P S q w (Sum.inl (Sum.inr ⟨q,e⟩)) = w e :=
  extend_reindex_at _ (qSyndromeEquiv P S q) w e
end QEC.Coding.BDL26RXDecoderAdapter

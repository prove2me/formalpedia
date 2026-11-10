-- Prove2me | solution 1 for QEC.Coding.BDL26RXDecoderAdapter.qExtend_at_q
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T02:47:05.487117+00:00
-- url     : https://prove2.me/submissions/c659be6b-e07c-4e67-a7bd-87eaf24e745c

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
theorem _root_.solution (P : TannerSquarePresentation) (S : OddScale) (q : P.Q)
    (w : Word BDL26Field (QDoubleCylinderVertex P q S)) (a : QDoubleCylinderVertex P q S) :
    qExtend P S q w (Sum.inr ⟨q,a⟩) = w a :=
  extend_reindex_at _ (qCorrectionEquiv P S q) w a
end QEC.Coding.BDL26RXDecoderAdapter

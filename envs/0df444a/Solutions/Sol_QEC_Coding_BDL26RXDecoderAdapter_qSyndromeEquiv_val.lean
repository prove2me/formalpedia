-- Prove2me | solution 1 for QEC.Coding.BDL26RXDecoderAdapter.qSyndromeEquiv_val
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T01:54:48.619631+00:00
-- url     : https://prove2.me/submissions/59dfc6b1-3e98-4805-a806-fff1f5e973ca

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_IndexedDecoder
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXStagedRestriction
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalWeightCertificates
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Regions

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXDecoderAdapter
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementSupport BDL26DecodingGraph MultiscaleDecoder
open scoped Classical
namespace QEC.Coding.BDL26RXDecoderAdapter
theorem _root_.solution (P : TannerSquarePresentation) (S : OddScale)
    (q : P.Q) (e : QDoubleCylinderEdge P q S) :
    (qSyndromeEquiv P S q e).1 = Sum.inl (Sum.inr ⟨q,e⟩) := rfl
end QEC.Coding.BDL26RXDecoderAdapter

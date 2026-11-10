-- Prove2me | solution 1 for QEC.Coding.BDL26RXDecoderAdapter.qCorrectionEquiv_val
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T01:53:29.625825+00:00
-- url     : https://prove2.me/submissions/fe6bafe1-6c26-4ef3-92ac-947a5e62ddaf

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
    (q : P.Q) (v : QDoubleCylinderVertex P q S) :
    (qCorrectionEquiv P S q v).1 = Sum.inr ⟨q,v⟩ := rfl
end QEC.Coding.BDL26RXDecoderAdapter

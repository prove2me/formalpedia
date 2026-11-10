-- Prove2me | solution 1 for QEC.Coding.BDL26RXDecoderAdapter.xSyndromeEquiv_val
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T01:55:25.080911+00:00
-- url     : https://prove2.me/submissions/6ac6dcd4-d60c-4564-a98f-3ac4ad7d7d13

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
    (x : P.X) (f : DoubleCylinderFace P x S) :
    (xSyndromeEquiv P S x f).1 = Sum.inl (Sum.inl ⟨x,f⟩) := rfl
end QEC.Coding.BDL26RXDecoderAdapter

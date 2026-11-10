-- Prove2me | solution 1 for QEC.Coding.BDL26RXDecoderAdapter.xCorrectionEquiv_val
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T01:54:00.699288+00:00
-- url     : https://prove2.me/submissions/fb033920-f150-4bb1-87be-9ce599c00b75

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
    (x : P.X) (e : DoubleCylinderEdge P x S) :
    (xCorrectionEquiv P S x e).1 = Sum.inl ⟨x,e⟩ := rfl
end QEC.Coding.BDL26RXDecoderAdapter

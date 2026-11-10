-- Prove2me | solution 1 for QEC.Coding.BDL26RXDecoderAdapter.zPairEquiv_val
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T01:57:19.629828+00:00
-- url     : https://prove2.me/submissions/56f6c39e-21e2-451c-b92e-934c3b2fe48e

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Regions
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Sectors

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXDecoderAdapter
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementSupport BDL26ReplacementCochainMaps BDL26RXStagedRestriction
open BDL26DecodingGraph MultiscaleDecoder
open scoped Classical BigOperators
namespace QEC.Coding.BDL26RXDecoderAdapter
theorem _root_.solution (P : TannerSquarePresentation) (S : OddScale)
    (p : P.Z × Fin 2) : (zPairEquiv P S p).val = Sum.inr p := rfl
end QEC.Coding.BDL26RXDecoderAdapter

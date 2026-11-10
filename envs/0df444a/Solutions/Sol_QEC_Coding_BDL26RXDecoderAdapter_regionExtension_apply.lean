-- Prove2me | solution 1 for QEC.Coding.BDL26RXDecoderAdapter.regionExtension_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T02:10:33.383207+00:00
-- url     : https://prove2.me/submissions/406ffb2a-f653-41d1-8c75-41d3f2530957

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Coordinates
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Flow

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXDecoderAdapter
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementSupport BDL26ReplacementCochainMaps BDL26RXStagedRestriction
open BDL26DecodingGraph MultiscaleDecoder
open scoped Classical BigOperators
namespace QEC.Coding.BDL26RXDecoderAdapter
theorem _root_.solution {A : Type} [Fintype A] [DecidableEq A]
    (Y : Finset A) (w : Word BDL26Field (LocalRegionIndex Y)) (p : A) :
    extendWordLinear Y w p = extendLocalSignal Y w p := rfl
end QEC.Coding.BDL26RXDecoderAdapter

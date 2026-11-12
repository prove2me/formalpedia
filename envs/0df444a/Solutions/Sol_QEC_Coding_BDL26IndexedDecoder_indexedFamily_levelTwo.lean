-- Prove2me | solution 1 for QEC.Coding.BDL26IndexedDecoder.indexedFamily_levelTwo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T22:04:12.413057+00:00
-- url     : https://prove2.me/submissions/79862d07-1338-4b9d-9ea0-8fd964d479c3

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDecoder
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_IndexedDecoder

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26IndexedDecoder
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26ReplacementCochainMaps BDL26RZLocalReplacement BDL26RXLocalReplacement
open BDL26RZMap1CoordinateBridge
open MultiscaleDecoder BDL26AlternatingCochain
open scoped Classical
universe u
namespace QEC.Coding.BDL26IndexedDecoder
theorem _root_.solution (S : OddScale) :
    indexedFamily S 2 = BDL26LevelTwoDecoder.decoderFamily S := rfl
end QEC.Coding.BDL26IndexedDecoder

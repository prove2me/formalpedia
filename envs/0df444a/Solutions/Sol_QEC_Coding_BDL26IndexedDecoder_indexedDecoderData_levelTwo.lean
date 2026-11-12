-- Prove2me | solution 1 for QEC.Coding.BDL26IndexedDecoder.indexedDecoderData_levelTwo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T22:05:22.852109+00:00
-- url     : https://prove2.me/submissions/e663c9b4-dede-4f6f-80c0-972b09c8d5b4

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
theorem _root_.solution (S : OddScale) (i : StepIndex 2) :
    ((indexedDecoderData S 2).selectedMap i).map0 =
      ((BDL26LevelTwoDecoder.decoderData S).selectedMap i).map0 ∧
    ((indexedDecoderData S 2).selectedMap i).map1 =
      ((BDL26LevelTwoDecoder.decoderData S).selectedMap i).map1 ∧
    ((indexedDecoderData S 2).selectedMap i).map2 =
      ((BDL26LevelTwoDecoder.decoderData S).selectedMap i).map2 := by
  fin_cases i <;> exact ⟨rfl, rfl, rfl⟩
end QEC.Coding.BDL26IndexedDecoder

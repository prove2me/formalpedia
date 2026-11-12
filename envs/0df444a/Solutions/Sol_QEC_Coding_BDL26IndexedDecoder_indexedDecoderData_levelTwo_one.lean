-- Prove2me | solution 1 for QEC.Coding.BDL26IndexedDecoder.indexedDecoderData_levelTwo_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T22:05:19.527936+00:00
-- url     : https://prove2.me/submissions/f16064d6-c59f-4e55-9d91-d5928c47d939

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDecoder
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_IndexedDecoder
import Theorems.Thm_QEC_Coding_BDL26IndexedDecoder_selectedMap_eq

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
    ((indexedDecoderData S 2).selectedMap (1 : StepIndex 2)).map0 =
      ((BDL26LevelTwoDecoder.decoderData S).selectedMap (1 : StepIndex 2)).map0 ∧
    ((indexedDecoderData S 2).selectedMap (1 : StepIndex 2)).map1 =
      ((BDL26LevelTwoDecoder.decoderData S).selectedMap (1 : StepIndex 2)).map1 ∧
    ((indexedDecoderData S 2).selectedMap (1 : StepIndex 2)).map2 =
      ((BDL26LevelTwoDecoder.decoderData S).selectedMap (1 : StepIndex 2)).map2 := by
  rw [selectedMap_eq]
  exact ⟨rfl, rfl, rfl⟩
end QEC.Coding.BDL26IndexedDecoder

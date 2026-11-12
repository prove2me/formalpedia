-- Prove2me | solution 1 for QEC.Coding.BDL26IndexedDecoder.indexedDecoderData_levelTwo_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T22:04:26.045465+00:00
-- url     : https://prove2.me/submissions/d4ce511e-1e07-4cac-8ae5-7b84efbdf12f

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
    ((indexedDecoderData S 2).selectedMap (0 : StepIndex 2)).map0 =
      (rxMap baseTannerSquarePresentation S).map0 ∧
    ((indexedDecoderData S 2).selectedMap (0 : StepIndex 2)).map1 =
      (rxMap baseTannerSquarePresentation S).map1 ∧
    ((indexedDecoderData S 2).selectedMap (0 : StepIndex 2)).map2 =
      (rxMap baseTannerSquarePresentation S).map2 := by
  rw [selectedMap_eq]
  exact ⟨rfl, rfl, rfl⟩
end QEC.Coding.BDL26IndexedDecoder

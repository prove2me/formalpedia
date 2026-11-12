-- Prove2me | solution 1 for QEC.Coding.BDL26RZPhysicalXStarTransport.composed_syndrome
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T23:33:26.108148+00:00
-- url     : https://prove2.me/submissions/d6d5e2ea-c544-44ae-aad8-7cebb920c15d

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXPhysicalStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Snapshots
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalXStarTransport
import Theorems.Thm_QEC_Coding_BDL26RZPhysicalXStarTransport_adjacent_RX

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RZPhysicalXStarTransport
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26DecodingGraph BDL26IndexedDecoder BDL26RZLocalReplacement
open BDL26RZMap1CoordinateBridge BDL26ReplacementSupport BDL26LevelTwoDistance
open BDL26ReplacementCochainMaps BDL26RZDecoderAdapter BDL26RZErrorPullback
open BDL26RZFiniteBlockTransport MultiscaleDecoder
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (odd : ¬i.val%2=0)
namespace QEC.Coding.BDL26RZPhysicalXStarTransport
theorem _root_.solution (S : OddScale) (j : Nat) (u : FamilyX S (2*j+4) (topStep j).succ)
    (a b : Upper S (2*j+4) (topStep j))
    (he : Localized S (2*j+4) (topStep j) u a b) :
    (indexedFamily S (2*j+4)).coboundary1 (topStep j).succ
      (((indexedDecoderData S (2*j+4)).selectedMap (topStep j)).map1
        (((indexedDecoderData S (2*j+4)).selectedMap (rxStep j)).map1 (secondLower S j u a b)))=
      ((indexedDecoderData S (2*j+4)).selectedMap (topStep j)).map2
        (((indexedDecoderData S (2*j+4)).selectedMap (rxStep j)).map2
          ((nextOutput S j a).coarse.val+(nextOutput S j b).coarse.val)) := by
  have hZ := LinearMap.congr_fun
    (((indexedDecoderData S (2*j+4)).selectedMap (topStep j)).commutes_coboundary1)
    (((indexedDecoderData S (2*j+4)).selectedMap (rxStep j)).map1 (secondLower S j u a b))
  have hX := LinearMap.congr_fun
    (((indexedDecoderData S (2*j+4)).selectedMap (rxStep j)).commutes_coboundary1)
    (secondLower S j u a b)
  calc
    _ = ((indexedDecoderData S (2*j+4)).selectedMap (topStep j)).map2
        ((indexedFamily S (2*j+4)).coboundary1 (rxStep j).succ
          (((indexedDecoderData S (2*j+4)).selectedMap (rxStep j)).map1 (secondLower S j u a b))) := hZ
    _ = ((indexedDecoderData S (2*j+4)).selectedMap (topStep j)).map2
        (((indexedDecoderData S (2*j+4)).selectedMap (rxStep j)).map2
          ((indexedFamily S (2*j+4)).coboundary1 (rxStep j).castSucc (secondLower S j u a b))) :=
      congrArg (((indexedDecoderData S (2*j+4)).selectedMap (topStep j)).map2) hX
    _ = _ := by rw [(adjacent_RX S j u a b he).2.2.1]
end QEC.Coding.BDL26RZPhysicalXStarTransport

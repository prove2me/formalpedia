-- Prove2me | solution 1 for QEC.Coding.BDL26RZPhysicalXStarTransport.composed_boundary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T17:11:47.702024+00:00
-- url     : https://prove2.me/submissions/d749535b-061c-4f45-abab-0061443eb964

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXPhysicalStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Snapshots
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalXStarTransport

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
    (a b : Upper S (2*j+4) (topStep j)) (p : Potential S (2*j+4) (topStep j)) :
    (indexedFamily S (2*j+4)).coboundary0 (topStep j).succ (composedPotential S j u a b p)=
      (indexedFamily S (2*j+4)).coboundary0 (topStep j).succ p+
      ((indexedDecoderData S (2*j+4)).selectedMap (topStep j)).map1
        ((indexedFamily S (2*j+4)).coboundary0 (rxStep j).succ (secondPotential S j u a b)) := by
  rw [composedPotential,map_add]
  have h := LinearMap.congr_fun
    (((indexedDecoderData S (2*j+4)).selectedMap (topStep j)).commutes_coboundary0)
    (secondPotential S j u a b)
  exact congrArg (fun w => (indexedFamily S (2*j+4)).coboundary0 (topStep j).succ p+w) h
end QEC.Coding.BDL26RZPhysicalXStarTransport

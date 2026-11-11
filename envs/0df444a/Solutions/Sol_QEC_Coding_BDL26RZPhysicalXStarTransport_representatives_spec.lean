-- Prove2me | solution 1 for QEC.Coding.BDL26RZPhysicalXStarTransport.representatives_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T17:18:33.817484+00:00
-- url     : https://prove2.me/submissions/7638e2b9-8714-409e-8022-a9c4e7c4e053

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXPhysicalStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Snapshots
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalXStarTransport
import Theorems.Thm_QEC_Coding_BDL26RZPhysicalXStarTransport_firstRepresentative_spec
import Theorems.Thm_QEC_Coding_BDL26RZFiniteBlockTransport_lowerError_delta

section
noncomputable section
namespace QEC.Coding.BDL26RZPhysicalXStarTransport
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26DecodingGraph BDL26IndexedDecoder BDL26RZLocalReplacement
open BDL26RZMap1CoordinateBridge BDL26ReplacementSupport BDL26LevelTwoDistance
open BDL26ReplacementCochainMaps BDL26RZDecoderAdapter BDL26RZErrorPullback
open BDL26RZFiniteBlockTransport MultiscaleDecoder
open scoped Classical BigOperators
private theorem twice {I : Type} (w : Word BDL26FiniteTannerSquare.Field I) : w+w=0 := by
  funext q
  exact CharTwo.add_self_eq_zero _
private theorem shift {I : Type} (a e : Word BDL26FiniteTannerSquare.Field I) : a+(a+e)=e := by
  rw [← add_assoc,twice,zero_add]
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (odd : ¬i.val%2=0)
section HistoryBridge
open BDL26HistorySyndromeSensitivity
end HistoryBridge
section Adjacent
end Adjacent
end QEC.Coding.BDL26RZPhysicalXStarTransport
end
end

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
theorem _root_.solution (S : OddScale) (j : Nat) (a b : Upper S (2*j+4) (topStep j)) :
    (indexedFamily S (2*j+4)).coboundary1 (rxStep j).succ (firstRepresentative S j a)=
      (run S (2*j+4) (topStep j) (topStep_odd j) a).coarse.val ∧
    (indexedFamily S (2*j+4)).coboundary1 (rxStep j).succ (secondRepresentative S j a b)=
      (run S (2*j+4) (topStep j) (topStep_odd j) b).coarse.val ∧
    firstRepresentative S j a+secondRepresentative S j a b=firstLower S j a b := by
  refine ⟨firstRepresentative_spec S j a,?_,?_⟩
  · rw [secondRepresentative,map_add,firstRepresentative_spec]
    have hl := lowerError_delta S (2*j+4) (topStep j) (topStep_odd j) a b
    change (indexedFamily S (2*j+4)).coboundary1 (rxStep j).succ (firstLower S j a b)=_ at hl
    rw [hl]
    let zA : Word BDL26FiniteTannerSquare.Field (state S (2*j+3)).presentation.Z :=
      (run S (2*j+4) (topStep j) (topStep_odd j) a).coarse.val
    let zB : Word BDL26FiniteTannerSquare.Field (state S (2*j+3)).presentation.Z :=
      (run S (2*j+4) (topStep j) (topStep_odd j) b).coarse.val
    change zA+(zA+zB)=zB
    exact shift zA zB
  · change firstRepresentative S j a+(firstRepresentative S j a+firstLower S j a b)=_
    exact shift _ _
end QEC.Coding.BDL26RZPhysicalXStarTransport

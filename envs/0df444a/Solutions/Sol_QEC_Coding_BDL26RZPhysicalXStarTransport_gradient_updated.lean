-- Prove2me | solution 1 for QEC.Coding.BDL26RZPhysicalXStarTransport.gradient_updated
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T17:12:37.481759+00:00
-- url     : https://prove2.me/submissions/d2a28eb1-6d3e-4200-be8f-1c30828e4297

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXPhysicalStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Snapshots
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalXStarTransport
import Theorems.Thm_QEC_Coding_BDL26RZPhysicalXStarTransport_gradient_run_eq
import Theorems.Thm_QEC_Coding_BDL26RXPhysicalStarTransport_gradient_run_eq

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
theorem _root_.solution (u : FamilyX S depth i.succ) (a : Upper S depth i) :
    updated S depth i odd a (a+gradient S depth i u)=gradient S depth i u := by
  unfold updated
  rw [gradient_run_eq,shift,add_assoc,twice,add_zero]
end QEC.Coding.BDL26RZPhysicalXStarTransport

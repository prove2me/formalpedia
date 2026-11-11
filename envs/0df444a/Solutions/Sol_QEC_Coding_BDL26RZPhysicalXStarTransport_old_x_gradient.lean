-- Prove2me | solution 1 for QEC.Coding.BDL26RZPhysicalXStarTransport.old_x_gradient
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T17:04:04.429048+00:00
-- url     : https://prove2.me/submissions/f8955baf-2db7-4b50-bcf3-8f2cf4468c87

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXPhysicalStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Snapshots
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalXStarTransport
import Theorems.Thm_QEC_Coding_BDL26RZPhysicalXStarTransport_lower_gradient_coordinates

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
theorem _root_.solution (x : (Old S depth i).X) (c : BDL26FiniteTannerSquare.Two) (a : Upper S depth i) :
    lowerError S depth i odd a (a+gradient S depth i (upperXChart S depth i odd (.inr (x,c))))=
      tannerCoboundary0 (Old S depth i) (canonicalBasisWord (F := BDL26FiniteTannerSquare.Field) x) := by
  rw [lower_gradient_coordinates]
  exact rzQParity_oldX_coboundary _ _ _ _ _
end QEC.Coding.BDL26RZPhysicalXStarTransport

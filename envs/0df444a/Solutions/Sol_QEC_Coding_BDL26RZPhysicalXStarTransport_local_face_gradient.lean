-- Prove2me | solution 1 for QEC.Coding.BDL26RZPhysicalXStarTransport.local_face_gradient
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T23:29:24.323703+00:00
-- url     : https://prove2.me/submissions/7892d90c-4529-411f-a6f8-039bd7122cf8

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
theorem _root_.solution (z : (Old S depth i).Z) (f : ZDoubleCylinderFace (Old S depth i) z S)
    (a : Upper S depth i) :
    lowerError S depth i odd a (a+gradient S depth i (upperXChart S depth i odd (.inl (.inl ⟨z,f⟩))))=0 := by
  rw [lower_gradient_coordinates]
  exact rzQParity_localFace_coboundary _ _ _ _ _
end QEC.Coding.BDL26RZPhysicalXStarTransport

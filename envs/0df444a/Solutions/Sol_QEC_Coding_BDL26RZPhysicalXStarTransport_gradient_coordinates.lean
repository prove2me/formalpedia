-- Prove2me | solution 1 for QEC.Coding.BDL26RZPhysicalXStarTransport.gradient_coordinates
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T17:00:07.577542+00:00
-- url     : https://prove2.me/submissions/68dacf1d-ab11-4d2d-babb-94dea66950b8

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXPhysicalStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Snapshots
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalXStarTransport
import Theorems.Thm_QEC_Coding_BDL26RZPhysicalXStarTransport_read0_basis
import Theorems.Thm_QEC_Coding_BDL26RZFiniteBlockTransport_delta0_coordinates


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
theorem _root_.solution (x : RZX (Old S depth i) S) :
    read1 S depth i odd (gradient S depth i (upperXChart S depth i odd x))=
      rzCoboundary0 (Old S depth i) (state S i.val).admissible S
        (canonicalBasisWord (F := BDL26FiniteTannerSquare.Field) x) := by
  rw [gradient,delta0_coordinates,read0_basis]
end QEC.Coding.BDL26RZPhysicalXStarTransport

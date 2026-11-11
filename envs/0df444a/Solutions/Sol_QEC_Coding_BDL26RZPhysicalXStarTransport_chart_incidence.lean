-- Prove2me | solution 1 for QEC.Coding.BDL26RZPhysicalXStarTransport.chart_incidence
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T16:51:41.123205+00:00
-- url     : https://prove2.me/submissions/6d137d56-d4ff-4ff4-bd21-a2b3de8b5893

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXPhysicalStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Snapshots
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalXStarTransport
import Theorems.Thm_QEC_Coding_BDL26RZPhysicalXStarTransport_actual_incidence
import Theorems.Thm_QEC_Coding_BDL26RZPhysicalStarTransport_actual_incidence


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
theorem _root_.solution (x : RZX (Old S depth i) S) (r : RZQ (Old S depth i) S) :
    (state S (i.val+1)).presentation.xq
      (upperXChart S depth i odd x) (upperQChart S depth i odd r)=
      rzXQIncidence (Old S depth i) (state S i.val).admissible.toTannerSquareAdmissible S x r := by
  rw [actual_incidence S depth i odd,coord0_chart,coord1_chart]
end QEC.Coding.BDL26RZPhysicalXStarTransport

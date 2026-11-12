-- Prove2me | solution 1 for QEC.Coding.BDL26RZFiniteBlockTransport.old_x_star
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T23:14:24.382004+00:00
-- url     : https://prove2.me/submissions/fba64479-c3c5-4cb5-bd00-823e7b0aa2df

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZErrorPullback
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZFiniteBlockTransport
import Theorems.Thm_QEC_Coding_BDL26RZFiniteBlockTransport_two_run
import Theorems.Thm_QEC_Coding_BDL26RZErrorPullback_two_run


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RZFiniteBlockTransport
open BDL26FiniteAlternatingCore
open Classical BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26RZLocalReplacement BDL26RZMap1CoordinateBridge BDL26ReplacementSupport
open BDL26ReplacementCochainMaps BDL26LevelTwoDistance BDL26IndexedDecoder
open MultiscaleDecoder RZCoarseGraining RZCoarseGrainingData
open scoped BigOperators Classical
open BDL26RZDecoderAdapter BDL26RZErrorPullback
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (odd : ¬i.val % 2=0)
namespace QEC.Coding.BDL26RZFiniteBlockTransport
theorem _root_.solution (above : 2 ≤ i.val) (x : (Old S depth i).X) (a b : Upper S depth i)
    (he : hammingSupport (a+b) ⊆ inputBlocks S depth i odd
      (incidentQ S depth i x) (Coordinates.neighborZ (Old S depth i) (incidentQ S depth i x))) :
    ∃ p : Potential S depth i, Pullback S depth i odd
      (incidentQ S depth i x) (Coordinates.neighborZ (Old S depth i) (incidentQ S depth i x)) a b p :=
  two_run S depth i odd above _ _ a b he
end QEC.Coding.BDL26RZFiniteBlockTransport

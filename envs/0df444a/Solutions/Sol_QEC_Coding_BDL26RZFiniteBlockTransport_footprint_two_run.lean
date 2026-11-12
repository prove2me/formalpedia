-- Prove2me | solution 1 for QEC.Coding.BDL26RZFiniteBlockTransport.footprint_two_run
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T23:14:12.065592+00:00
-- url     : https://prove2.me/submissions/d06e0f76-2334-463b-830f-fd51cc69efea

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZErrorPullback
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZFiniteBlockTransport
import Theorems.Thm_QEC_Coding_BDL26RZFiniteBlockTransport_two_run
import Theorems.Thm_QEC_Coding_BDL26RZFiniteBlockTransport_footprint_localized
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
theorem _root_.solution (above : 2 ≤ i.val) (a b : Upper S depth i) :
    ∃ p : Potential S depth i, Pullback S depth i odd
      (footprintQ S depth i odd a b) (footprintZ S depth i odd a b) a b p :=
  two_run S depth i odd above _ _ a b (footprint_localized S depth i odd a b)
end QEC.Coding.BDL26RZFiniteBlockTransport

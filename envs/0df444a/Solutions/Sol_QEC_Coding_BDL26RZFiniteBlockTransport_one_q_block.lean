-- Prove2me | solution 1 for QEC.Coding.BDL26RZFiniteBlockTransport.one_q_block
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T12:13:24.896064+00:00
-- url     : https://prove2.me/submissions/af34f620-3f2f-4501-bcee-9b7279be6abc

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZErrorPullback
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZFiniteBlockTransport
import Theorems.Thm_QEC_Coding_BDL26RZFiniteBlockTransport_two_run
import Theorems.Thm_QEC_Coding_BDL26RZErrorPullback_two_run
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans


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
theorem _root_.solution (above : 2 ≤ i.val) (q : (Old S depth i).Q)
    (a b : Upper S depth i) (he : hammingSupport (a+b) ⊆ qBlocks S depth i odd {q}) :
    ∃ p : Potential S depth i, Pullback S depth i odd {q} ∅ a b p := by
  apply two_run S depth i odd above
  exact he.trans Finset.subset_union_left
end QEC.Coding.BDL26RZFiniteBlockTransport

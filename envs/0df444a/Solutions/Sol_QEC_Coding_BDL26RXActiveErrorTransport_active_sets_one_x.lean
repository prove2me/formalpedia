-- Prove2me | solution 1 for QEC.Coding.BDL26RXActiveErrorTransport.active_sets_one_x
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T03:18:57.897432+00:00
-- url     : https://prove2.me/submissions/9a451f62-4c9a-4cf8-bab6-13a7ba3eb6ad

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXFiniteBlockTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXActiveErrorTransport
import Theorems.Thm_QEC_Coding_BDL26RXActiveErrorTransport_active_x_of_restriction_ne_zero
import Theorems.Thm_QEC_Coding_BDL26RXActiveErrorTransport_activeX_subset_of_support
import Theorems.Thm_QEC_Coding_BDL26RXActiveErrorTransport_activeQ_subset_of_support

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXActiveErrorTransport
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RXDecoderAdapter BDL26RXErrorPullback
open BDL26RZMap1CoordinateBridge BDL26RXXStarTransport MultiscaleDecoder RXCoarseGraining
open RXCoarseGraining.RXCoarseGrainingData
open BDL26BoundedValence BDL26GraphQuantitativeBounds
open scoped BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (h : i.val % 2=0)
namespace QEC.Coding.BDL26RXActiveErrorTransport
theorem _root_.solution (x : XCoord S i) (E : Upper S depth i)
    (he : hammingSupport E ⊆ (rxLx S depth i h).correctionRegion x)
    (hn : restrictWordLinear ((rxLx S depth i h).correctionRegion x) E≠0) :
    activeX S depth i h E={x} ∧ activeQ S depth i h E=∅ := by
  have hs : hammingSupport E ⊆ BDL26RXFiniteBlockTransport.xBlocks S depth i h {x} ∪
      BDL26RXFiniteBlockTransport.qBlocks S depth i h ∅ := by
    intro p hp
    exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨x,Finset.mem_singleton_self _,he hp⟩)
  exact ⟨Finset.Subset.antisymm (activeX_subset_of_support S depth i h {x} ∅ E hs)
      (Finset.singleton_subset_iff.mpr (active_x_of_restriction_ne_zero S depth i h E x hn)),
    Finset.subset_empty.mp (activeQ_subset_of_support S depth i h {x} ∅ E hs)⟩
end QEC.Coding.BDL26RXActiveErrorTransport

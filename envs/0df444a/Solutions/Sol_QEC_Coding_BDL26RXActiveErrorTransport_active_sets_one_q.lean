-- Prove2me | solution 1 for QEC.Coding.BDL26RXActiveErrorTransport.active_sets_one_q
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T03:19:12.793674+00:00
-- url     : https://prove2.me/submissions/c0b5d101-d0c4-4628-a4aa-2b3a30c5aaa4

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXFiniteBlockTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXActiveErrorTransport
import Theorems.Thm_QEC_Coding_BDL26RXActiveErrorTransport_active_q_of_restriction_ne_zero
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
theorem _root_.solution (q : QCoord S i) (E : Upper S depth i)
    (he : hammingSupport E ⊆ (rxLq S depth i h).correctionRegion q)
    (hn : restrictWordLinear ((rxLq S depth i h).correctionRegion q) E≠0) :
    activeX S depth i h E=∅ ∧ activeQ S depth i h E={q} := by
  have hs : hammingSupport E ⊆ BDL26RXFiniteBlockTransport.xBlocks S depth i h ∅ ∪
      BDL26RXFiniteBlockTransport.qBlocks S depth i h {q} := by
    intro p hp
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨q,Finset.mem_singleton_self _,he hp⟩)
  exact ⟨Finset.subset_empty.mp (activeX_subset_of_support S depth i h ∅ {q} E hs),
    Finset.Subset.antisymm (activeQ_subset_of_support S depth i h ∅ {q} E hs)
      (Finset.singleton_subset_iff.mpr (active_q_of_restriction_ne_zero S depth i h E q hn))⟩
end QEC.Coding.BDL26RXActiveErrorTransport

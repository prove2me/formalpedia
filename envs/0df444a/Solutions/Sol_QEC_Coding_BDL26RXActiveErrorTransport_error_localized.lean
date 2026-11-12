-- Prove2me | solution 1 for QEC.Coding.BDL26RXActiveErrorTransport.error_localized
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T10:51:09.287749+00:00
-- url     : https://prove2.me/submissions/edb29196-401e-4a0c-9cc8-429f47cdde47

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXFiniteBlockTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXActiveErrorTransport
import Theorems.Thm_QEC_Coding_BDL26RXActiveErrorTransport_support_partition
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


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
theorem _root_.solution (E : Upper S depth i) :
    hammingSupport E ⊆ BDL26RXFiniteBlockTransport.xBlocks S depth i h (activeX S depth i h E) ∪
      BDL26RXFiniteBlockTransport.qBlocks S depth i h (activeQ S depth i h E) := by
  intro p hp
  have hm := (support_partition S depth i h E).symm ▸ hp
  rcases Finset.mem_union.mp hm with hm | hm
  · obtain ⟨x,hx,hp⟩ := Finset.mem_biUnion.mp hm
    exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨x,hx,(Finset.mem_inter.mp hp).1⟩)
  · obtain ⟨q,hq,hp⟩ := Finset.mem_biUnion.mp hm
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨q,hq,(Finset.mem_inter.mp hp).1⟩)
end QEC.Coding.BDL26RXActiveErrorTransport

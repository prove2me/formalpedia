-- Prove2me | solution 1 for QEC.Coding.BDL26RXActiveErrorTransport.support_partition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T10:46:51.552945+00:00
-- url     : https://prove2.me/submissions/41cd0027-fa52-4df8-8fd2-0a9fbc56e8e1

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXFiniteBlockTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXActiveErrorTransport
import Theorems.Thm_QEC_Coding_BDL26RXActiveErrorTransport_mem_activeX
import Theorems.Thm_QEC_Coding_BDL26RXActiveErrorTransport_mem_activeQ
import Theorems.Thm_QEC_Coding_BDL26RXActiveErrorTransport_correction_regions_cover

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
    (activeX S depth i h E).biUnion (xPiece S depth i h E) ∪
      (activeQ S depth i h E).biUnion (qPiece S depth i h E)=hammingSupport E := by
  ext p
  constructor
  · intro hp
    rcases Finset.mem_union.mp hp with hp | hp
    · obtain ⟨x,_,hx⟩ := Finset.mem_biUnion.mp hp
      exact (Finset.mem_inter.mp hx).2
    · obtain ⟨q,_,hq⟩ := Finset.mem_biUnion.mp hp
      exact (Finset.mem_inter.mp hq).2
  · intro hp
    have hc : p ∈ (Finset.univ.biUnion ((rxLx S depth i h).correctionRegion)) ∪
        (Finset.univ.biUnion ((rxLq S depth i h).correctionRegion)) := by
      rw [correction_regions_cover S depth i h]
      exact Finset.mem_univ _
    rcases Finset.mem_union.mp hc with hc | hc
    · obtain ⟨x,_,hx⟩ := Finset.mem_biUnion.mp hc
      have hm : p ∈ xPiece S depth i h E x := Finset.mem_inter.mpr ⟨hx,hp⟩
      exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr
        ⟨x,(mem_activeX S depth i h E x).mpr ⟨p,hm⟩,hm⟩)
    · obtain ⟨q,_,hq⟩ := Finset.mem_biUnion.mp hc
      have hm : p ∈ qPiece S depth i h E q := Finset.mem_inter.mpr ⟨hq,hp⟩
      exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨q,(mem_activeQ S depth i h E q).mpr ⟨p,hm⟩,hm⟩)
end QEC.Coding.BDL26RXActiveErrorTransport

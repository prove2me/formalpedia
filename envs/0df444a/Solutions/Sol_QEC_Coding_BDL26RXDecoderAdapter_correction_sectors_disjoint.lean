-- Prove2me | solution 1 for QEC.Coding.BDL26RXDecoderAdapter.correction_sectors_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T02:12:23.293623+00:00
-- url     : https://prove2.me/submissions/60eb74ab-8016-4a78-a571-d65506078e06

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Regions
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Sectors
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm

section
namespace QEC.Coding.BDL26RXDecoderAdapter
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementSupport BDL26ReplacementCochainMaps BDL26RXStagedRestriction
open BDL26DecodingGraph MultiscaleDecoder
open scoped Classical BigOperators
private theorem mem_qCorrectionSector (P : TannerSquarePresentation) (S : OddScale) (p : RX1 P S) :
    p ∈ qCorrectionSector P S ↔ ∃ q, rxCorrectionOwner P S p = Vertex.q q := by
  exact Finset.mem_filter.trans (and_iff_right (Finset.mem_univ p))
end QEC.Coding.BDL26RXDecoderAdapter
end

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXDecoderAdapter
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementSupport BDL26ReplacementCochainMaps BDL26RXStagedRestriction
open BDL26DecodingGraph MultiscaleDecoder
open scoped Classical BigOperators
namespace QEC.Coding.BDL26RXDecoderAdapter
theorem _root_.solution (P : TannerSquarePresentation) (S : OddScale) :
    Disjoint (RXCoarseGraining.correctionRegionUnion (localX P S))
      (qCorrectionSector P S) := by
  apply Finset.disjoint_left.mpr
  intro p hx hq
  obtain ⟨x,_,hx⟩ := Finset.mem_biUnion.mp hx
  obtain ⟨q,hq⟩ := (mem_qCorrectionSector P S p).mp hq
  have hx : rxCorrectionOwner P S p = Vertex.x x := (Finset.mem_filter.mp hx).2
  have h := hx.symm.trans hq
  cases h
end QEC.Coding.BDL26RXDecoderAdapter

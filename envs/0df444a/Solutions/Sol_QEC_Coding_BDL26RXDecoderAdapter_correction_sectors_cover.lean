-- Prove2me | solution 1 for QEC.Coding.BDL26RXDecoderAdapter.correction_sectors_cover
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T01:59:50.63521+00:00
-- url     : https://prove2.me/submissions/d336ab22-bb00-4011-8434-6e426db7c211

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Regions
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Sectors
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans

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
    RXCoarseGraining.correctionRegionUnion (localX P S) ∪ qCorrectionSector P S =
      Finset.univ := by
  apply Finset.ext
  intro p
  constructor
  · intro _; exact Finset.mem_univ p
  · intro _
    rcases p with ⟨x,e⟩ | ⟨q,v⟩
    · apply Finset.mem_union_left
      apply Finset.mem_biUnion.mpr
      exact ⟨x, Finset.mem_univ _, (xCorrectionEquiv P S x e).2⟩
    · exact Finset.mem_union_right _ ((mem_qCorrectionSector P S _).mpr ⟨q,rfl⟩)
end QEC.Coding.BDL26RXDecoderAdapter

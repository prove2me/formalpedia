-- Prove2me | solution 1 for QEC.Coding.BDL26RXDecoderAdapter.syndrome_sectors_cover
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T04:44:18.81208+00:00
-- url     : https://prove2.me/submissions/5735f883-45f2-4711-82e7-5e58f73fa146

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Regions
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Sectors
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans

section
namespace QEC.Coding.BDL26RXDecoderAdapter
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementSupport BDL26ReplacementCochainMaps BDL26RXStagedRestriction
open BDL26DecodingGraph MultiscaleDecoder
open scoped Classical BigOperators
private theorem mem_xSector (P : TannerSquarePresentation) (S : OddScale) (p : RX2 P S) :
    p ∈ xSector P S ↔ ∃ x, rxSyndromeOwner P S p = Vertex.x x := by
  exact Finset.mem_filter.trans (and_iff_right (Finset.mem_univ p))
private theorem mem_qSector (P : TannerSquarePresentation) (S : OddScale) (p : RX2 P S) :
    p ∈ qSector P S ↔ ∃ q, rxSyndromeOwner P S p = Vertex.q q := by
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
    xSector P S ∪ qSector P S ∪ zSector P S = Finset.univ := by
  apply Finset.ext
  intro p
  constructor
  · intro _; exact Finset.mem_univ p
  · intro _
    rcases p with (⟨x,f⟩ | ⟨q,e⟩) | ⟨z,c⟩
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ ((mem_xSector P S _).mpr ⟨x,rfl⟩))
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ ((mem_qSector P S _).mpr ⟨q,rfl⟩))
    · exact Finset.mem_union_right _ ((mem_zSector P S _).mpr ⟨z,rfl⟩)
end QEC.Coding.BDL26RXDecoderAdapter

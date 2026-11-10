-- Prove2me | solution 1 for QEC.Coding.BDL26RXDecoderAdapter.syndrome_sectors_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T04:45:51.961631+00:00
-- url     : https://prove2.me/submissions/1741d65c-f324-4f62-80dc-45d09001c300

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
    Disjoint (xSector P S) (qSector P S) ∧ Disjoint (xSector P S) (zSector P S) ∧
      Disjoint (qSector P S) (zSector P S) := by
  refine ⟨Finset.disjoint_left.mpr ?_, Finset.disjoint_left.mpr ?_, Finset.disjoint_left.mpr ?_⟩
  · intro p hx hq
    obtain ⟨x,hx⟩ := (mem_xSector P S p).mp hx
    obtain ⟨q,hq⟩ := (mem_qSector P S p).mp hq
    have h := hx.symm.trans hq
    cases h
  · intro p hx hz
    obtain ⟨x,hx⟩ := (mem_xSector P S p).mp hx
    obtain ⟨z,hz⟩ := (mem_zSector P S p).mp hz
    have h := hx.symm.trans hz
    cases h
  · intro p hq hz
    obtain ⟨q,hq⟩ := (mem_qSector P S p).mp hq
    obtain ⟨z,hz⟩ := (mem_zSector P S p).mp hz
    have h := hq.symm.trans hz
    cases h
end QEC.Coding.BDL26RXDecoderAdapter

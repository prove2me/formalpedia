-- Prove2me | solution 1 for ThreeSum.LightSourceBandHistSelect.right_ends
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:11:54.18573+00:00
-- url     : https://prove2.me/submissions/15c06b2b-89fe-49ff-8fa0-50f2fe4637af

import Definitions.Def_Submission_ThreeSum_SourceBandPairSlices
import Definitions.Def_Submission_ThreeSum_LightSourceBandHistSelect
import Theorems.Thm_ThreeSum_LightSourceBandHistSelect_finish_ends
import Theorems.Thm_Light_Ends_next
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_Arithmetic_missWeight_zero
import Theorems.Thm_ThreeSum_BandPartition_size_le
import Theorems.Thm_ThreeSum_BlockCoefficientRows_mapRow_fin
import Theorems.Thm_ThreeSum_BlockCoefficientRows_occurrenceIndices_fin
import Theorems.Thm_ThreeSum_BlockEncoding_leftSubset_fromSubsets
import Theorems.Thm_ThreeSum_BlockEncoding_rightSubset_fromSubsets
import Theorems.Thm_ThreeSum_BlockEncoding_row_leftSubset
import Theorems.Thm_ThreeSum_BlockEncoding_row_outputSubset
import Theorems.Thm_ThreeSum_BlockEncoding_row_rightSubset
import Theorems.Thm_ThreeSum_BlockIndex_coordEquiv_val
import Theorems.Thm_ThreeSum_BlockIndex_indexSet_card
import Theorems.Thm_ThreeSum_BlockIndex_indexSet_subset
import Theorems.Thm_ThreeSum_BlockIndex_indexSet_union
import Theorems.Thm_ThreeSum_BlockIndex_index_unindex
import Theorems.Thm_ThreeSum_BlockIndex_mem_indexSet
import Theorems.Thm_ThreeSum_BlockIndex_unindex_index
import Theorems.Thm_ThreeSum_BlockIndexedQuery_prefixIndices_card
import Theorems.Thm_ThreeSum_BlockRows_flat_row
import Theorems.Thm_ThreeSum_BlockRows_mem_flat
import Theorems.Thm_ThreeSum_BlockRows_mem_join
import Theorems.Thm_ThreeSum_BlockRows_mem_prefixIndices
import Theorems.Thm_ThreeSum_BlockRows_mem_row
import Theorems.Thm_ThreeSum_BlockRows_row_flat
import Theorems.Thm_ThreeSum_BlockRows_row_inter
import Theorems.Thm_ThreeSum_BlockRows_row_join
import Theorems.Thm_ThreeSum_BlockRows_row_sdiff
import Theorems.Thm_ThreeSum_BlockRows_row_union
import Theorems.Thm_ThreeSum_BlockSourceEncoding_modulus_cast
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Theorems.Thm_ThreeSum_LightHistogram_count_zero
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_output_length
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_output_zero
import Theorems.Thm_ThreeSum_OneHotMask_extend_fin
import Theorems.Thm_ThreeSum_OneHotMask_mem_natPositions
import Theorems.Thm_ThreeSum_SourceBandLayout_flat_end_le_work
import Theorems.Thm_ThreeSum_SourceBandLayout_header_end
import Theorems.Thm_ThreeSum_SourceBandPairData_ordered
import Theorems.Thm_ThreeSum_SourceBandPairSlices_heads_read
import Theorems.Thm_ThreeSum_SourceBandPairSlices_right_end
import Theorems.Thm_ThreeSum_SourceBuckets_offset_zero
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_zero
import Theorems.Thm_ThreeSum_SubsetAddress_natPositions_card
import Theorems.Thm_ThreeSum_SubsetAddress_weight_zero
import Theorems.Thm_ThreeSum_SubsetStages_mem_suffix
import Theorems.Thm_ThreeSum_SubsetStages_stageValue_all
import Theorems.Thm_ThreeSum_SubsetStages_stageValue_zero
import Theorems.Thm_ThreeSum_SubsetStages_suffix_all
import Theorems.Thm_ThreeSum_SubsetStages_suffix_zero
import Theorems.Thm_ThreeSum_SubsetTransport_reindex_map
attribute [local simp] Light.getElem_powList
attribute [local simp] Light.length_powList
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.Arithmetic.missWeight_zero
attribute [local simp] ThreeSum.BlockCoefficientRows.mapRow_fin
attribute [local simp] ThreeSum.BlockCoefficientRows.occurrenceIndices_fin
attribute [local simp] ThreeSum.BlockEncoding.leftSubset_fromSubsets
attribute [local simp] ThreeSum.BlockEncoding.rightSubset_fromSubsets
attribute [local simp] ThreeSum.BlockEncoding.row_leftSubset
attribute [local simp] ThreeSum.BlockEncoding.row_outputSubset
attribute [local simp] ThreeSum.BlockEncoding.row_rightSubset
attribute [local simp] ThreeSum.BlockIndex.coordEquiv_val
attribute [local simp] ThreeSum.BlockIndex.indexSet_card
attribute [local simp] ThreeSum.BlockIndex.indexSet_subset
attribute [local simp] ThreeSum.BlockIndex.indexSet_union
attribute [local simp] ThreeSum.BlockIndex.index_unindex
attribute [local simp] ThreeSum.BlockIndex.mem_indexSet
attribute [local simp] ThreeSum.BlockIndex.unindex_index
attribute [local simp] ThreeSum.BlockIndexedQuery.prefixIndices_card
attribute [local simp] ThreeSum.BlockRows.flat_row
attribute [local simp] ThreeSum.BlockRows.mem_flat
attribute [local simp] ThreeSum.BlockRows.mem_join
attribute [local simp] ThreeSum.BlockRows.mem_prefixIndices
attribute [local simp] ThreeSum.BlockRows.mem_row
attribute [local simp] ThreeSum.BlockRows.row_flat
attribute [local simp] ThreeSum.BlockRows.row_inter
attribute [local simp] ThreeSum.BlockRows.row_join
attribute [local simp] ThreeSum.BlockRows.row_sdiff
attribute [local simp] ThreeSum.BlockRows.row_union
attribute [local simp] ThreeSum.BlockSourceEncoding.modulus_cast
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices
attribute [local simp] ThreeSum.LightHistogram.count_zero
attribute [local simp] ThreeSum.LightSubsetEnumeration.output_length
attribute [local simp] ThreeSum.LightSubsetEnumeration.output_zero
attribute [local simp] ThreeSum.OneHotMask.extend_fin
attribute [local simp] ThreeSum.OneHotMask.mem_natPositions
attribute [local simp] ThreeSum.SourceBuckets.offset_zero
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero
attribute [local simp] ThreeSum.SubsetStages.mem_suffix
attribute [local simp] ThreeSum.SubsetStages.stageValue_all
attribute [local simp] ThreeSum.SubsetStages.stageValue_zero
attribute [local simp] ThreeSum.SubsetStages.suffix_all
attribute [local simp] ThreeSum.SubsetStages.suffix_zero
attribute [local simp] ThreeSum.SubsetTransport.reindex_map
set_option autoImplicit false
open ThreeSum ThreeSum.LightSourceBandHistSelect
open Light BandPartition SourceBandPairData SourceBandPairSlices
set_option maxHeartbeats 2500000
set_option maxRecDepth 12000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightSourceBandHistSelect
theorem _root_.solution {μ : ℕ → ℤ} {fL fR : ℕ → ℤ} {pair NL NR g p m i dst left : ℕ} {shift : ℤ}
    (H : Stored μ fL fR pair NL NR g p m shift) (hw : (lim.space : ℤ) ≤ lim.word) (hm : 0 < m)
    (hb : next pair NL NR g m ≤ dst) (hs : dst + 2 ≤ lim.space) (hwN : ((NL + NR + i + 6 : ℕ) : ℤ) ≤ lim.word)
    (hl : left ≤ lim.space) :
    Ends lim P d rightBody ⟨frame [pair, i, dst, left, zeroBase pair NL NR g m], μ⟩ 200
      (fun σ => σ.mem dst = (left : ℤ) ∧ σ.mem (dst + 1) = (histRight pair NL NR g m i : ℤ) ∧ Kept μ σ.mem dst) :=
  by
  obtain ⟨hbaseL, hcountL, hbaseR, hcountR, hzero, _⟩ := heads_read H
  have ho := ordered pair NL NR g m
  have hcounts := size_le NR g
  have hcountWord : (size NR g : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (show size NR g ≤ NL + NR + i + 6 by omega)).trans hwN
  have hindexWord : (i : ℤ) ≤ lim.word := (Int.ofNat_le.mpr (by omega : i ≤ NL + NR + i + 6)).trans hwN
  have h6 : (6 : ℤ) ≤ lim.word := by omega
  have hheadBound : pair + 8 ≤ dst := by unfold leftBase at ho; omega
  have hzeroBound : zeroBase pair NL NR g m ≤ lim.space := by omega
  have htarget := right_end pair NL NR g m i
  have haddr2 : ((pair : ℤ) + 2).toNat = pair + 2 := by omega
  have haddr3 : ((pair : ℤ) + 3).toNat = pair + 3 := by omega
  unfold rightBody
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      repeat
        with_unfolding_none
          first
          | refine _root_.Light.Ends.seqAssoc ?_
          | refine _root_.Light.Ends.skipThen ?_)
    refine _root_.Light.Ends.iteIffThen ((i : ℤ) < (size NR g : ℤ)) (fun hy => ?_) (fun hn => ?_) ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hcountR, haddr3]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hcountR, haddr3] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hcountR, haddr3] <;> omega)
    all_goals
      repeat
        with_unfolding_none
          first
          | refine _root_.Light.Ends.seqAssoc ?_
          | refine _root_.Light.Ends.skipThen ?_
  · have hi : i < size NR g := by omega
    have hhead := SourceBandLayout.header_end (base := rightBase pair NL g m) (m := m) hi
    have hend := SourceBandLayout.flat_end_le_work (base := rightBase pair NL g m) (m := m) hi
    change
      SourceBandLayout.flat (rightBase pair NL g m) NR g m i + SourceBandLayout.cap NR g ≤
        zeroBase pair NL NR g m at hend
    unfold SourceBandLayout.flat SourceBandLayout.cursor SourceBandLayout.offsets SourceBandLayout.codes at hend
    have haddr : ((rightBase pair NL g m : ℤ) + 6 * (i : ℤ) + 3).toNat = rightBase pair NL g m + 6 * i + 3 := by omega
    have haddrWord : (rightBase pair NL g m : ℤ) + 6 * (i : ℤ) + 3 < lim.space := by
      exact_mod_cast (by omega : rightBase pair NL g m + 6 * i + 3 < lim.space)
    have hprod : (6 : ℤ) * (i : ℤ) ≤ lim.word := by omega
    have hread := (H.right i hi).headHist
    have he : histRight pair NL NR g m i = SourceBandLayout.hist (rightBase pair NL g m) NR g m i := by
      simp only [histRight, histogramPtr, if_pos hi]
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_)
      refine _root_.Light.Ends.setToThen (SourceBandLayout.hist (rightBase pair NL g m) NR g m i : ℕ) ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hbaseR, haddr2,
              haddr, hread]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [hbaseR, haddr2, haddr, hread] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hbaseR, haddr2, haddr, hread] <;> omega)
      try with_unfolding_none refine _root_.Light.Ends.skip ?_
    rw [he]
    focus
      (refine
          _root_.Light.Ends.pieceLast (finish_ends hw hs hl (by omega))
            (fun _ h_p2m_17370607848908311011 => h_p2m_17370607848908311011) ?_;
        on_goal -1 =>
          first
          | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
              first
              | omega
              | (ring_nf; omega))
          | omega
          |
            (simp [] <;>
                first
                | omega
                | (ring_nf; omega)))
  · have hi : ¬i < size NR g := by omega
    have he : histRight pair NL NR g m i = zeroBase pair NL NR g m := by simp only [histRight, histogramPtr, if_neg hi]
    rw [he]
    focus
      (refine
          _root_.Light.Ends.pieceLast (finish_ends hw hs hl hzeroBound)
            (fun _ h_p2m_6723936638599758505 => h_p2m_6723936638599758505) ?_;
        on_goal -1 =>
          first
          | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
              first
              | omega
              | (ring_nf; omega))
          | omega
          |
            (simp [] <;>
                first
                | omega
                | (ring_nf; omega)))
end ThreeSum.LightSourceBandHistSelect

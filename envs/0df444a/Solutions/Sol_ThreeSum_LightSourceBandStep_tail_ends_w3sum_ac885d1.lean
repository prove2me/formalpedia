-- Prove2me | solution 1 for ThreeSum.LightSourceBandStep.tail_ends_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:32:36.488904+00:00
-- url     : https://prove2.me/submissions/1ce6e8d7-38a9-4997-8a32-356934aaf80a

import Definitions.Def_Submission_ThreeSum_SourceBandData
import Definitions.Def_Submission_ThreeSum_LightSourceBandStep
import Theorems.Thm_ThreeSum_LightSourceBandStep_original_time_le
import Theorems.Thm_Light_Meets_mono_time
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_Arithmetic_missWeight_zero
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
import Definitions.Def_WeightedCache3SUM_Alias_9c326f345c0ba28d
import Definitions.Def_WeightedCache3SUM_Alias_244efc85702348f3
import Definitions.Def_WeightedCache3SUM_Alias_31257a44f822c74e
import Theorems.Thm_ThreeSum_LightHistogram_count_zero
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Definitions.Def_WeightedCache3SUM_Alias_d061ef657958844a
import Definitions.Def_WeightedCache3SUM_Alias_aeb4de5e6b301b55
import Theorems.Thm_ThreeSum_LightScaleArray_meets
import Definitions.Def_WeightedCache3SUM_Alias_8c6e823b5fcef3e6
import Definitions.Def_WeightedCache3SUM_Alias_3b570d79c28763f9
import Definitions.Def_WeightedCache3SUM_Alias_2968a7144f4e39f0
import Definitions.Def_WeightedCache3SUM_Alias_075817043fa4e845
import Theorems.Thm_ThreeSum_LightSourceBuild_Procs_meets
import Definitions.Def_WeightedCache3SUM_Alias_27f79aa230fbddf9
import Definitions.Def_WeightedCache3SUM_Alias_5b14bc7229a63f1e
import Theorems.Thm_ThreeSum_LightSourceResidues_meets
import Definitions.Def_WeightedCache3SUM_Alias_ce5ff1e60c39fd21
import Theorems.Thm_ThreeSum_LightSourceStages_Procs_meets
import Theorems.Thm_ThreeSum_LightSourceStages_ZetaProcs_meets
import Definitions.Def_WeightedCache3SUM_Alias_f29d07b5f5ce2e2c
import Definitions.Def_WeightedCache3SUM_Alias_098d503c7eb426c7
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_output_length
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_output_zero
import Definitions.Def_WeightedCache3SUM_Alias_037fdff845f4735d
import Definitions.Def_WeightedCache3SUM_Alias_8a94481881de516b
import Definitions.Def_WeightedCache3SUM_Alias_c0e528b1e0cee255
import Definitions.Def_WeightedCache3SUM_Alias_44f02ed11cdb23f7
import Definitions.Def_WeightedCache3SUM_Alias_d110f06b53aa1a96
import Definitions.Def_WeightedCache3SUM_Alias_197272b1cee37ac5
import Theorems.Thm_ThreeSum_OneHotMask_extend_fin
import Theorems.Thm_ThreeSum_OneHotMask_mem_natPositions
import Theorems.Thm_ThreeSum_SourceBandLayout_buckets_congr
import Theorems.Thm_ThreeSum_SourceBandLayout_count_congr
import Theorems.Thm_ThreeSum_SourceBandLayout_data_le_hist
import Theorems.Thm_ThreeSum_SourceBandLayout_flat_end_le_work
import Theorems.Thm_ThreeSum_SourceBandLayout_header_end
import Theorems.Thm_ThreeSum_SourceBandLayout_input_index
import Theorems.Thm_ThreeSum_SourceBandLayout_len_le_cap
import Theorems.Thm_ThreeSum_SourceBandLayout_start_add_len
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
open ThreeSum ThreeSum.LightSourceBandStep
open Light BandPartition SourceBandLayout
set_option maxHeartbeats 3000000
set_option maxRecDepth 18000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightSourceBandStep
theorem _root_.solution {pOriginal : ℕ} (C : LightSourceBucketOriginal.Procs P pOriginal) {μ : ℕ → ℤ}
    {src n g p m base U D i last : ℕ} {shift : ℤ} (f : ℕ → ℤ) (hw : (lim.space : ℤ) ≤ lim.word) (hd : d + 3 < lim.depth)
    (hg : 0 < g) (hp : 0 < p) (hm : 0 < m) (hi : i < size n g) (hsrc : src + n ≤ base) (hlast : last = stop n g i)
    (hspace : LightSourceResidues.space (work base n g m) p U D ≤ lim.space) (hshift : |shift| ≤ (D : ℤ))
    (hword : (word n g p m U D : ℤ) ≤ lim.word) (hread : ∀ j < n, μ (src + j) = f j)
    (hvalues : ∀ j < n, |f j| ≤ (U : ℤ)) :
    Ends lim P d (tailBody pOriginal)
      ⟨frame
          [src, n, g, p, m, shift, base, cap n g, size n g, data base n g, stride n g m, work base n g m, i, start g i,
            last],
        μ⟩
      (tailTime n g p m U D)
      (fun σ =>
        SourceBandData.At σ.mem f base n g p m shift i ∧ KeptBut μ σ.mem (hist base n g m i) (base + 6 * i) 6) :=
  by
  subst last
  have hwork : work base n g m ≤ lim.space :=
    by
    unfold LightSourceResidues.space at hspace
    omega
  have hcap := len_le_cap n g i
  have hflat := flat_end_le_work (base := base) (m := m) hi
  have hhead := header_end (base := base) (m := m) hi
  have hdata := data_le_hist base n g m i
  have hhist : hist base n g m i ≤ work base n g m :=
    by
    unfold flat cursor offsets codes at hflat
    omega
  have hb : base ≤ hist base n g m i := by unfold data at hdata; omega
  have hstop := stop_le n g i
  have hstart := start_lt_stop hg hi
  have hlen := start_add_len hg hi
  have hprod : (i : ℤ) * (stride n g m : ℤ) ≤ lim.word :=
    (by exact_mod_cast (show i * stride n g m ≤ lim.space by unfold hist at hhist; omega) :
          (i : ℤ) * (stride n g m : ℤ) ≤ lim.space).trans
      hw
  have hprodN : (0 : ℤ) ≤ (i : ℤ) * (stride n g m : ℤ) := by positivity
  have hheadprod : (6 : ℤ) * (i : ℤ) ≤ lim.word :=
    (by exact_mod_cast (show 6 * i ≤ lim.space by omega) : (6 : ℤ) * (i : ℤ) ≤ lim.space).trans hw
  have hcodes : codes base n g m i ≤ work base n g m :=
    by
    unfold flat cursor offsets at hflat
    omega
  have hoffsets : offsets base n g m i ≤ work base n g m :=
    by
    unfold flat cursor at hflat
    omega
  have hcursor : cursor base n g m i ≤ work base n g m := by unfold flat at hflat; omega
  have hhistAddr : (data base n g : ℤ) + (i : ℤ) * (stride n g m : ℤ) ≤ lim.word :=
    (by exact_mod_cast (hhist.trans hwork) : (data base n g : ℤ) + (i : ℤ) * (stride n g m : ℤ) ≤ lim.space).trans hw
  have hcodesAddr : hist base n g m i + m ≤ lim.space := hcodes.trans hwork
  have hoffsetsAddr : codes base n g m i + cap n g ≤ lim.space := hoffsets.trans hwork
  have hcursorAddr : offsets base n g m i + m + 1 ≤ lim.space := hcursor.trans hwork
  have hflatAddr : cursor base n g m i + m ≤ lim.space := by unfold flat at hflat; omega
  have hword' : (LightSourceResidues.word p m U D : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (show LightSourceResidues.word p m U D ≤ word n g p m U D by unfold word; omega)).trans hword
  unfold tailBody tailTime
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    refine _root_.Light.Ends.setToThen (len n g i : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, len]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [len] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, len] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    refine _root_.Light.Ends.setToThen (hist base n g m i : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hist]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hist] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hist] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    refine _root_.Light.Ends.setToThen (codes base n g m i : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, codes]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [codes] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, codes] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    refine _root_.Light.Ends.setToThen (offsets base n g m i : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, offsets]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [offsets] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, offsets] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    refine _root_.Light.Ends.setToThen (cursor base n g m i : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, cursor]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [cursor] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, cursor] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    refine _root_.Light.Ends.setToThen (flat base n g m i : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, flat]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [flat] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, flat] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  have horiginal :=
    C.meets (d := d + 1) (μ := μ) (src := src + start g i) (N := len n g i) (p := p) (m := m) (shift := shift) (hist :=
      hist base n g m i) (codes := codes base n g m i) (offsets := offsets base n g m i) (cursor := cursor base n g m i)
      (flat := flat base n g m i) (work := work base n g m) (U := U) (D := D) hw (by omega) hp hm (by omega) le_rfl
      (by unfold offsets; omega) le_rfl le_rfl (by omega) hspace hshift hword'
      (by
        intro j hj
        have hj' := input_index hg hi hj
        rw [Nat.add_assoc, hread _ hj']
        exact hvalues _ hj')
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    first
    |
      refine
        _root_.Light.Ends.callToThen ((horiginal.mono_time (original_time_le n g p m U D i)) _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen (horiginal.mono_time (original_time_le n g p m U D i)) ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
    on_goal -1 => (rintro r ν ⟨buckets, counts, keys, kept⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    refine _root_.Light.Ends.storeToThen (base + 6 * i) (start g i : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    refine _root_.Light.Ends.storeToThen (base + 6 * i + 1) (len n g i : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    refine _root_.Light.Ends.storeToThen (base + 6 * i + 2) (codes base n g m i : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    refine _root_.Light.Ends.storeToThen (base + 6 * i + 3) (hist base n g m i : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    refine _root_.Light.Ends.storeToThen (base + 6 * i + 4) (offsets base n g m i : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    refine _root_.Light.Ends.storeToThen (base + 6 * i + 5) (flat base n g m i : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  dsimp only
  have hkey : ∀ j < len n g i, LightSourceResidues.key p m shift (μ (src + start g i + j)) = key f g p m shift i j :=
    by
    intro j hj
    rw [Nat.add_assoc, hread _ (input_index hg hi hj)]
    rfl
  have stored := buckets_congr buckets hkey
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ⟨?_, ?_⟩⟩, ?_⟩
  ·
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_self]
  ·
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega), Function.update_self]
  ·
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_self]
  · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_self]
  · rw [Function.update_of_ne (by omega), Function.update_self]
  · exact Function.update_self ..
  · intro j hj
    have ha : base + 6 * i + 6 ≤ codes base n g m i + j := by unfold codes; omega
    repeat' rw [Function.update_of_ne (by omega)]
    exact (keys j hj).trans (congrArg Int.ofNat (hkey j hj))
  · intro q hq
    repeat' rw [Function.update_of_ne (by omega)]
    exact (counts q hq).trans (congrArg Int.ofNat (count_congr hkey le_rfl q))
  · intro q hq
    have ha : base + 6 * i + 6 ≤ offsets base n g m i + q := by unfold offsets codes; omega
    repeat' rw [Function.update_of_ne (by omega)]
    exact stored.offsets q hq
  · intro j hj
    have ha : base + 6 * i + 6 ≤ flat base n g m i + SourceBuckets.position (key f g p m shift i) (len n g i) j :=
      by
      unfold flat cursor offsets codes
      omega
    repeat' rw [Function.update_of_ne (by omega)]
    exact stored.indices j hj
  · intro x hx
    repeat' rw [Function.update_of_ne (by omega)]
    exact kept x hx.1
end ThreeSum.LightSourceBandStep

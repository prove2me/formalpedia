-- Prove2me | solution 1 for ThreeSum.LightCoverKeys.Procs.meets_with_masks_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:58:26.380774+00:00
-- url     : https://prove2.me/submissions/6f5c8a03-9689-43b3-9ca5-b7bb4ea6455f

import Definitions.Def_Submission_ThreeSum_LightLocalCoverRetention
import Definitions.Def_Submission_ThreeSum_LightGlobalKeys
import Definitions.Def_Submission_ThreeSum_LightCoverKeys
import Theorems.Thm_Light_Ends_next
import Theorems.Thm_Light_Meets_of_body
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
import Theorems.Thm_ThreeSum_CyclicFold_asPolynomial_replicate_zero
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_coeff
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_minus
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_negate
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_plus
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_shift
import Theorems.Thm_ThreeSum_Karatsuba_length_minus
import Theorems.Thm_ThreeSum_Karatsuba_length_negate
import Theorems.Thm_ThreeSum_Karatsuba_length_plus
import Theorems.Thm_ThreeSum_Karatsuba_length_shift
import Theorems.Thm_ThreeSum_Karatsuba_minus_getD
import Theorems.Thm_ThreeSum_Karatsuba_plus_getD
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Definitions.Def_WeightedCache3SUM_Alias_9c326f345c0ba28d
import Definitions.Def_WeightedCache3SUM_Alias_d7235e9f603abd3f
import Definitions.Def_WeightedCache3SUM_Alias_f318d8b49c9fc733
import Definitions.Def_WeightedCache3SUM_Alias_2b9c97c844160a97
import Theorems.Thm_ThreeSum_LightCoverSelect_Procs_meets
import Theorems.Thm_ThreeSum_LightCoverSelect_meets
import Definitions.Def_WeightedCache3SUM_Alias_7c6295bca57f98dc
import Theorems.Thm_ThreeSum_LightGlobalKeys_Procs_meets
import Definitions.Def_WeightedCache3SUM_Alias_188c0aebc110975b
import Theorems.Thm_ThreeSum_LightHashHistogram_Procs_meets
import Theorems.Thm_ThreeSum_LightHistogram_count_zero
import Definitions.Def_WeightedCache3SUM_Alias_9f151fd16c06b1ef
import Definitions.Def_WeightedCache3SUM_Alias_2311045817689c86
import Definitions.Def_WeightedCache3SUM_Alias_d5eaa25d4585cc6b
import Definitions.Def_WeightedCache3SUM_Alias_da105011ac4dcdd4
import Definitions.Def_WeightedCache3SUM_Alias_942628883105a84f
import Definitions.Def_WeightedCache3SUM_Alias_8622643736b2cec4
import Definitions.Def_WeightedCache3SUM_Alias_04fc0611b78e7896
import Definitions.Def_WeightedCache3SUM_Alias_d3fb44062fe6c749
import Theorems.Thm_ThreeSum_LightLocalCoverRetention_base_le_nextFree
import Theorems.Thm_ThreeSum_LightLocalCoverRetention_data_of_kept
import Theorems.Thm_ThreeSum_LightLocalCoverRetention_header_of_kept
import Theorems.Thm_ThreeSum_LightLocalCoverRetention_indices_of_kept
import Theorems.Thm_ThreeSum_LightLocalCoverRetention_rows_of_kept
import Definitions.Def_WeightedCache3SUM_Alias_a64b3be7ea8b7b19
import Definitions.Def_WeightedCache3SUM_Alias_0a77a2090c5d3d77
import Definitions.Def_WeightedCache3SUM_Alias_eb65baeba73fd57c
import Definitions.Def_WeightedCache3SUM_Alias_3b3552e2795ab46d
import Definitions.Def_WeightedCache3SUM_Alias_e2ad5e59f3af6ab7
import Definitions.Def_WeightedCache3SUM_Alias_ed969675cd1be1e3
import Definitions.Def_WeightedCache3SUM_Alias_737c7144994f79de
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Definitions.Def_WeightedCache3SUM_Alias_d061ef657958844a
import Definitions.Def_WeightedCache3SUM_Alias_e1d95931a2ead3e4
import Definitions.Def_WeightedCache3SUM_Alias_d92129e9a4741fac
import Definitions.Def_WeightedCache3SUM_Alias_aeb4de5e6b301b55
import Definitions.Def_WeightedCache3SUM_Alias_9176929b72776235
import Theorems.Thm_ThreeSum_LightPrimality_Procs_meets
import Definitions.Def_WeightedCache3SUM_Alias_137b880911028d95
import Definitions.Def_WeightedCache3SUM_Alias_a00dee90c4e0ea45
import Definitions.Def_WeightedCache3SUM_Alias_e6a24ed55341e959
import Definitions.Def_WeightedCache3SUM_Alias_4b4040d8de1fb856
import Definitions.Def_WeightedCache3SUM_Alias_32e47c9a32bb047b
import Theorems.Thm_ThreeSum_LightReportingAffine_meets
import Definitions.Def_WeightedCache3SUM_Alias_9b3006da0fcbdf4e
import Theorems.Thm_ThreeSum_LightScaleArray_meets
import Definitions.Def_WeightedCache3SUM_Alias_276ab4baf5d9c1f3
import Definitions.Def_WeightedCache3SUM_Alias_73246870e6a638ab
import Definitions.Def_WeightedCache3SUM_Alias_f29d07b5f5ce2e2c
import Definitions.Def_WeightedCache3SUM_Alias_098d503c7eb426c7
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_output_length
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_output_zero
import Definitions.Def_WeightedCache3SUM_Alias_8a94481881de516b
import Definitions.Def_WeightedCache3SUM_Alias_66dd70707634c020
import Definitions.Def_WeightedCache3SUM_Alias_cdc5e7727f35fd80
import Definitions.Def_WeightedCache3SUM_Alias_de9d37b5900d1a92
import Definitions.Def_WeightedCache3SUM_Alias_a495b72bdff1a7b5
import Definitions.Def_WeightedCache3SUM_Alias_b5410f4bcc10d599
import Theorems.Thm_ThreeSum_OneHotMask_extend_fin
import Theorems.Thm_ThreeSum_OneHotMask_mem_natPositions
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_zero
import Theorems.Thm_ThreeSum_SubsetAddress_natPositions_card
import Theorems.Thm_ThreeSum_SubsetAddress_weight_zero
import Theorems.Thm_ThreeSum_WeightedScore_corrections_zero
import Theorems.Thm_ThreeSum_WeightedScore_remaining_zero
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
attribute [local simp] ThreeSum.CyclicFold.asPolynomial_replicate_zero
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_coeff
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_minus
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_negate
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_plus
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_shift
attribute [local simp] ThreeSum.Karatsuba.length_minus
attribute [local simp] ThreeSum.Karatsuba.length_negate
attribute [local simp] ThreeSum.Karatsuba.length_plus
attribute [local simp] ThreeSum.Karatsuba.length_shift
attribute [local simp] ThreeSum.Karatsuba.minus_getD
attribute [local simp] ThreeSum.Karatsuba.plus_getD
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices
attribute [local simp] ThreeSum.LightHistogram.count_zero
attribute [local simp] ThreeSum.LightSubsetEnumeration.output_length
attribute [local simp] ThreeSum.LightSubsetEnumeration.output_zero
attribute [local simp] ThreeSum.OneHotMask.extend_fin
attribute [local simp] ThreeSum.OneHotMask.mem_natPositions
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero
attribute [local simp] ThreeSum.WeightedScore.corrections_zero
attribute [local simp] ThreeSum.WeightedScore.remaining_zero
set_option autoImplicit false
open ThreeSum ThreeSum.LightCoverKeys
open Light GlobalEncoding GlobalKeyEnumeration LocalCoverBounds
open LightLocalCoverTables LightLocalCoverLayout LightLocalCoverSchedule
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightCoverKeys
namespace Procs
theorem _root_.solution {pMain h J free : ℕ} {μ : ℕ → ℤ} (S : Procs P pMain) (hw : (lim.space : ℤ) ≤ lim.word)
    (hd : d + 512 * h + J + 11 ≤ lim.depth) (hspace : space free h J ≤ lim.space) (hword : (word h J : ℤ) ≤ lim.word) :
    Meets lim P pMain d [h, J, free] μ (time h J)
      (fun r ν =>
        r = (keyHeader free h J : ℤ) ∧
          ν (keyHeader free h J) = ((LightGlobalKeys.localCount h ^ J : ℕ) : ℤ) ∧
            Seg ν (keyHeader free h J + 1) (globalKeys h J) ∧
              Seg ν free (LightLocalCoverInit.values free h) ∧
                Data ν h (maps (LightLocalCoverInit.base free) h) (hist0 (LightLocalCoverInit.base free) h)
                    (hist1 (LightLocalCoverInit.base free) h) (matrixPtr (LightLocalCoverInit.base free) h) ∧
                  ScheduleRows ν h (scheduleMaps (LightLocalCoverInit.base free) h) ∧
                    (∀ s : Occurrence h,
                        ν (candidates (LightLocalCoverInit.base free) h + s.val) = (candidateAt h s : ℤ)) ∧
                      (∀ i < outputCount (512 * h) h,
                          ν (afterCover free h + i) = (LocalMaskGraph.maskAt (512 * h) (2 * h) i : ℤ)) ∧
                        Kept μ ν free) :=
  by
  have hcspace : LightLocalCoverInit.space free h ≤ lim.space := (le_max_left _ _).trans hspace
  have hkspace : LightGlobalKeys.space (afterCover free h) h J ≤ lim.space := (le_max_right _ _).trans hspace
  have hcword : (LightLocalCoverInit.word h : ℤ) ≤ lim.word := (Int.ofNat_le.mpr (le_max_left _ _)).trans hword
  have hkword : (LightGlobalKeys.word h J : ℤ) ≤ lim.word := (Int.ofNat_le.mpr (le_max_right _ _)).trans hword
  have hbaseNext : free + 20 ≤ afterCover free h :=
    LightLocalCoverRetention.base_le_nextFree (LightLocalCoverInit.base free) h
  have hnextSpace : afterCover free h ≤ lim.space :=
    by
    have hs :
      LightLocalKeyRow.space (LightGlobalKeys.scratch (afterCover free h) h) (512 * h) (outputCount (512 * h) h) ≤
        lim.space :=
      (le_max_left _ _).trans hkspace
    unfold LightLocalKeyRow.space LightGlobalKeys.scratch at hs
    omega
  apply Meets.of_body S.main
  unfold body time
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
        _root_.Light.Ends.callToThen ((S.cover.meets (d := d + 1) hw (by omega) hcspace hcword) _ (by omega)) ?_ ?_ ?_
          ?_
    | refine _root_.Light.Ends.callToThen (S.cover.meets (d := d + 1) hw (by omega) hcspace hcword) ?_ ?_ ?_ ?_
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
    on_goal -1 =>
      (rintro next μ₁ ⟨hnext, hheader, hdata, hrows, hindices, hkeep₁⟩;
        try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have h0 : μ₁ free = (outputCount (512 * h) h : ℤ) := by
    simpa [LightLocalCoverInit.values, LightLocalParameters.values, LightLocalCounts.values,
      LightLocalCoverMetadata.values] using
      hheader 0
        (by
          simp [LightLocalCoverInit.values, LightLocalParameters.values, LightLocalCounts.values,
            LightLocalCoverMetadata.values])
  have h6 : μ₁ (free + 6) = (localPrime h : ℤ) := by
    simpa [LightLocalCoverInit.values, LightLocalParameters.values, LightLocalCounts.values,
      LightLocalCoverMetadata.values] using
      hheader 6
        (by
          simp [LightLocalCoverInit.values, LightLocalParameters.values, LightLocalCounts.values,
            LightLocalCoverMetadata.values])
  have h8 : μ₁ (free + 8) = (512 * h : ℤ) := by
    simpa [LightLocalCoverInit.values, LightLocalParameters.values, LightLocalCounts.values,
      LightLocalCoverMetadata.values] using
      hheader 8
        (by
          simp [LightLocalCoverInit.values, LightLocalParameters.values, LightLocalCounts.values,
            LightLocalCoverMetadata.values])
  have h9 : μ₁ (free + 9) = (2 * h : ℤ) := by
    simpa [LightLocalCoverInit.values, LightLocalParameters.values, LightLocalCounts.values,
      LightLocalCoverMetadata.values] using
      hheader 9
        (by
          simp [LightLocalCoverInit.values, LightLocalParameters.values, LightLocalCounts.values,
            LightLocalCoverMetadata.values])
  have h10 : μ₁ (free + 10) = (scheduleSize h : ℤ) := by
    simpa [LightLocalCoverInit.values, LightLocalParameters.values, LightLocalCounts.values,
      LightLocalCoverMetadata.values] using
      hheader 10
        (by
          simp [LightLocalCoverInit.values, LightLocalParameters.values, LightLocalCounts.values,
            LightLocalCoverMetadata.values])
  have h12 : μ₁ (free + 12) = (scheduleMaps (LightLocalCoverInit.base free) h : ℤ) := by
    simpa [LightLocalCoverInit.values, LightLocalParameters.values, LightLocalCounts.values,
      LightLocalCoverMetadata.values] using
      hheader 12
        (by
          simp [LightLocalCoverInit.values, LightLocalParameters.values, LightLocalCounts.values,
            LightLocalCoverMetadata.values])
  have hk :=
    S.keys.meets_with_masks (d := d + 1) (h := h) (J := J) (maps := scheduleMaps (LightLocalCoverInit.base free) h)
      (free := afterCover free h) hw (by omega) hkspace hkword le_rfl (fun j hj i hi => (hrows j hj i hi).1)
      (fun j hj i hi => (hrows j hj i hi).2)
  have haddress (i : ℕ) : ((free : ℤ) + (i : ℤ)).toNat = free + i := by omega
  have h6Read : μ₁ (((free : ℤ) + 6).toNat) = (localPrime h : ℤ) :=
    by
    rw [show ((free : ℤ) + 6).toNat = free + 6 by omega]
    exact h6
  have h8Read : μ₁ (((free : ℤ) + 8).toNat) = (512 * h : ℤ) :=
    by
    rw [show ((free : ℤ) + 8).toNat = free + 8 by omega]
    exact h8
  have h9Read : μ₁ (((free : ℤ) + 9).toNat) = (2 * h : ℤ) :=
    by
    rw [show ((free : ℤ) + 9).toNat = free + 9 by omega]
    exact h9
  have h10Read : μ₁ (((free : ℤ) + 10).toNat) = (scheduleSize h : ℤ) :=
    by
    rw [show ((free : ℤ) + 10).toNat = free + 10 by omega]
    exact h10
  have h12Read : μ₁ (((free : ℤ) + 12).toNat) = (scheduleMaps (LightLocalCoverInit.base free) h : ℤ) :=
    by
    rw [show ((free : ℤ) + 12).toNat = free + 12 by omega]
    exact h12
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
    | refine _root_.Light.Ends.callToThen (hk _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hk ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, h0, h6Read, h8Read, h9Read, h10Read,
            h12Read, hnext, afterCover]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [h0, h6Read, h8Read, h9Read, h10Read, h12Read, hnext, afterCover] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, h0, h6Read, h8Read, h9Read, h10Read, h12Read,
            hnext, afterCover] <;> omega)
    on_goal -1 =>
      (rintro result μ₂ ⟨hr, hcount, hkeys, hmasks, hkeep₂⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  refine
    ⟨hr, hcount, hkeys, LightLocalCoverRetention.header_of_kept hheader hkeep₂,
      LightLocalCoverRetention.data_of_kept hdata hkeep₂, LightLocalCoverRetention.rows_of_kept hrows hkeep₂,
      LightLocalCoverRetention.indices_of_kept hindices hkeep₂, hmasks, ?_⟩
  intro a ha
  exact (hkeep₂ a (by omega)).trans (hkeep₁ a ha)
end Procs
end ThreeSum.LightCoverKeys

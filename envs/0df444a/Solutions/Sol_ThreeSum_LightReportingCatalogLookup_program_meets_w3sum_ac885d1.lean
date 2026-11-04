-- Prove2me | solution 1 for ThreeSum.LightReportingCatalogLookup.program_meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T15:57:48.158989+00:00
-- url     : https://prove2.me/submissions/0f1550a3-aef0-48ff-9330-000f0e67cc7c

import Definitions.Def_Submission_ThreeSum_ReportingHostPackedCatalog
import Definitions.Def_Submission_ThreeSum_LightBandLookup
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Emod
import Definitions.Def_Submission_ThreeSum_LightReportingCatalogLookup
import Theorems.Thm_ThreeSum_LightReportingCatalogLookup_word_value
import Theorems.Thm_ThreeSum_LightReportingCatalogLookup_word_power
import Theorems.Thm_ThreeSum_LightReportingCatalogLookup_word_search
import Theorems.Thm_ThreeSum_LightReportingCatalogLookup_word_emod
import Theorems.Thm_Light_Meets_mono_time
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_emodRounds_le
import Definitions.Def_WeightedCache3SUM_Alias_6850731862e76136
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_powTable_meets
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_Arithmetic_missWeight_zero
import Theorems.Thm_ThreeSum_BinarySearch_upperBound_correct
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
import Theorems.Thm_ThreeSum_BlockMaskLayout_packedMasks_length
import Theorems.Thm_ThreeSum_BlockMaskLayout_prefixMask_all
import Theorems.Thm_ThreeSum_BlockMaskLayout_prefixMask_zero
import Theorems.Thm_ThreeSum_BlockMaskLayout_rawMasks_length
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
import Theorems.Thm_ThreeSum_BoxStages_mem_prefix
import Theorems.Thm_ThreeSum_BoxStages_prefix_all
import Theorems.Thm_ThreeSum_BoxStages_prefix_zero
import Theorems.Thm_ThreeSum_BoxStages_stageValue_all
import Theorems.Thm_ThreeSum_BoxStages_stageValue_zero
import Theorems.Thm_ThreeSum_ExplicitLayers_leaves_length
import Theorems.Thm_ThreeSum_ExplicitLayers_missing_length
import Theorems.Thm_ThreeSum_ExplicitLayers_valueSum_zero
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Definitions.Def_WeightedCache3SUM_Alias_b3ed31058dd4b298
import Theorems.Thm_ThreeSum_LightBoxSum_partialSum_length
import Theorems.Thm_ThreeSum_LightLeafSum_partialSum_length
import Theorems.Thm_ThreeSum_LightSubsetAddress_powers_of_segment
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_output_length
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_output_zero
import Theorems.Thm_ThreeSum_LightWeightedEnumeration_output_length
import Theorems.Thm_ThreeSum_LightWeightedEnumeration_output_zero
import Theorems.Thm_ThreeSum_LightWeightedEnumeration_total_succ
import Theorems.Thm_ThreeSum_LightWeightedEnumeration_total_zero
import Theorems.Thm_ThreeSum_MaskDifference_subsetMask_empty
import Theorems.Thm_ThreeSum_MaskUnion_scanSet_all
import Theorems.Thm_ThreeSum_MaskUnion_scanSet_zero
import Theorems.Thm_ThreeSum_OneHotMask_extend_fin
import Theorems.Thm_ThreeSum_OneHotMask_mem_natPositions
import Theorems.Thm_ThreeSum_QueryCoordinates_mem_positions
import Theorems.Thm_ThreeSum_QueryCoordinates_missingSets_length
import Theorems.Thm_ThreeSum_QueryCoordinates_positions_length
import Theorems.Thm_ThreeSum_QueryCoordinates_positions_toFinset
import Theorems.Thm_ThreeSum_QueryCoordinates_positions_zero
import Theorems.Thm_ThreeSum_QueryCoordinates_selectedPowers_length
import Theorems.Thm_ThreeSum_QueryCoordinates_selectedPowers_sum
import Theorems.Thm_ThreeSum_QueryCoordinates_selectedPowers_zero
import Theorems.Thm_ThreeSum_QueryCoordinates_setLayer_length
import Theorems.Thm_ThreeSum_QueryCoordinates_total_weights
import Theorems.Thm_ThreeSum_ReportingHostPackedCatalog_codes_length
import Theorems.Thm_ThreeSum_ReportingHostPackedCatalog_packed_emod
import Theorems.Thm_ThreeSum_ReportingHostPackedCatalog_packed_lt
import Theorems.Thm_ThreeSum_ReportingHostPackedCatalog_pairKey_lt
import Theorems.Thm_ThreeSum_ReportingHostPackedCatalog_sorted_getD_le
import Definitions.Def_WeightedCache3SUM_Alias_50296760f55bd93d
import Theorems.Thm_ThreeSum_ReportingHostPairSegments_leftMasks_length
import Theorems.Thm_ThreeSum_ReportingHostPairSegments_rightMasks_length
import Theorems.Thm_ThreeSum_ReportingHostSuffix_liftSet_card
import Theorems.Thm_ThreeSum_ReportingHostSuffix_liftSet_empty
import Theorems.Thm_ThreeSum_ReportingHostSuffix_mem_lowerSet
import Theorems.Thm_ThreeSum_ReportingHostSuffix_shiftEmbedding_val
import Theorems.Thm_ThreeSum_SignedLeaf_mem_explicitMissing
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
attribute [local simp] ThreeSum.BlockMaskLayout.packedMasks_length
attribute [local simp] ThreeSum.BlockMaskLayout.prefixMask_all
attribute [local simp] ThreeSum.BlockMaskLayout.prefixMask_zero
attribute [local simp] ThreeSum.BlockMaskLayout.rawMasks_length
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
attribute [local simp] ThreeSum.BoxStages.mem_prefix
attribute [local simp] ThreeSum.BoxStages.prefix_all
attribute [local simp] ThreeSum.BoxStages.prefix_zero
attribute [local simp] ThreeSum.BoxStages.stageValue_all
attribute [local simp] ThreeSum.BoxStages.stageValue_zero
attribute [local simp] ThreeSum.ExplicitLayers.leaves_length
attribute [local simp] ThreeSum.ExplicitLayers.missing_length
attribute [local simp] ThreeSum.ExplicitLayers.valueSum_zero
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices
attribute [local simp] ThreeSum.LightBoxSum.partialSum_length
attribute [local simp] ThreeSum.LightLeafSum.partialSum_length
attribute [local simp] ThreeSum.LightSubsetEnumeration.output_length
attribute [local simp] ThreeSum.LightSubsetEnumeration.output_zero
attribute [local simp] ThreeSum.LightWeightedEnumeration.output_length
attribute [local simp] ThreeSum.LightWeightedEnumeration.output_zero
attribute [local simp] ThreeSum.LightWeightedEnumeration.total_succ
attribute [local simp] ThreeSum.LightWeightedEnumeration.total_zero
attribute [local simp] ThreeSum.MaskDifference.subsetMask_empty
attribute [local simp] ThreeSum.MaskUnion.scanSet_all
attribute [local simp] ThreeSum.MaskUnion.scanSet_zero
attribute [local simp] ThreeSum.OneHotMask.extend_fin
attribute [local simp] ThreeSum.OneHotMask.mem_natPositions
attribute [local simp] ThreeSum.QueryCoordinates.mem_positions
attribute [local simp] ThreeSum.QueryCoordinates.missingSets_length
attribute [local simp] ThreeSum.QueryCoordinates.positions_length
attribute [local simp] ThreeSum.QueryCoordinates.positions_toFinset
attribute [local simp] ThreeSum.QueryCoordinates.positions_zero
attribute [local simp] ThreeSum.QueryCoordinates.selectedPowers_length
attribute [local simp] ThreeSum.QueryCoordinates.selectedPowers_sum
attribute [local simp] ThreeSum.QueryCoordinates.selectedPowers_zero
attribute [local simp] ThreeSum.QueryCoordinates.setLayer_length
attribute [local simp] ThreeSum.QueryCoordinates.total_weights
attribute [local simp] ThreeSum.ReportingHostPairSegments.leftMasks_length
attribute [local simp] ThreeSum.ReportingHostPairSegments.rightMasks_length
attribute [local simp] ThreeSum.ReportingHostSuffix.liftSet_card
attribute [local simp] ThreeSum.ReportingHostSuffix.liftSet_empty
attribute [local simp] ThreeSum.ReportingHostSuffix.mem_lowerSet
attribute [local simp] ThreeSum.ReportingHostSuffix.shiftEmbedding_val
attribute [local simp] ThreeSum.SignedLeaf.mem_explicitMissing
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
open ThreeSum ThreeSum.LightReportingCatalogLookup
open Light ThreeSum.LightPascal ThreeSum.LightSubsetAddress ReportingHostPackedCatalog
set_option maxHeartbeats 1500000
set_option maxRecDepth 8000
variable {lim : Limits}
namespace ThreeSum.LightReportingCatalogLookup
theorem _root_.solution {μ : ℕ → ℤ} {W n src work i d : ℕ} {S : List ℤ} (left right : ℕ → ℕ) (hi : i < n)
    (hw : (lim.space : ℤ) ≤ lim.word) (hsrc : src + n ≤ work) (hpowSpace : work + (2 * W + 2) ≤ lim.space)
    (hemodSpace : work + (Nat.log 2 (valueBound W n + 1) + 2) ≤ lim.space) (hword : (word W n : ℤ) ≤ lim.word)
    (hn : n ≤ 2 ^ (2 * W)) (hboundL : ∀ j < n, left j < 2 ^ W) (hboundR : ∀ j < n, right j < 2 ^ W)
    (hunique : ∀ a < n, ∀ b < n, pairKey (2 ^ W) (left a) (right a) = pairKey (2 ^ W) (left b) (right b) → a = b)
    (hperm : S.Perm (codes (fun j => pairKey (2 ^ W) (left j) (right j)) n)) (hsorted : S.Pairwise (· ≤ ·))
    (hseg : Seg μ src S) (hd : d + 2 * W + 2 ≤ lim.depth) :
    Meets lim program 3 d [W, n, src, left i, right i, work] μ (time W n) (fun r μ' => r = (i : ℤ) ∧ Kept μ μ' work) :=
  by
  let key : ℕ → ℕ := fun j => pairKey (2 ^ W) (left j) (right j)
  let threshold : ℕ := key i * (n + 1) + n
  let K := BinarySearch.upperBound (fun j => S.getD j 0) n (threshold : ℤ)
  have hlen : S.length = n := hperm.length_eq.trans (codes_length key n)
  have hkey : key i < 2 ^ (2 * W) := by
    simpa only [key, ← pow_mul, Nat.mul_comm] using pairKey_lt (hboundL i hi) (hboundR i hi)
  have hthreshold : threshold < valueBound W n := by unfold threshold valueBound; nlinarith
  have hcode : packed key n i < valueBound W n := packed_lt hi hkey
  have hUword : (valueBound W n : ℤ) ≤ lim.word := (Int.ofNat_le.mpr (word_value W n)).trans hword
  have hthWord : (threshold : ℤ) ≤ lim.word := (Int.ofNat_le.mpr hthreshold.le).trans hUword
  have hcodeWord : (packed key n i : ℤ) ≤ lim.word := (Int.ofNat_le.mpr hcode.le).trans hUword
  have hpowWord : ((2 ^ (2 * W + 2) : ℕ) : ℤ) ≤ lim.word := (Int.ofNat_le.mpr (word_power W n)).trans hword
  have hpowBound : ∀ j ≤ 2 * W + 2, ((2 ^ j : ℕ) : ℤ) ≤ lim.word :=
    by
    intro j hj
    exact (Int.ofNat_le.mpr (Nat.pow_le_pow_right (by decide) hj)).trans hpowWord
  have hsearchWord : ((n + 2 ^ ((2 * W + 1) + 1) + 16 : ℕ) : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (word_search W n)).trans hword
  have hEmod : Light.Emod.Pre lim (n + 1) (valueBound W n) work :=
    ⟨by omega, hw, by
      have hh := (Int.ofNat_le.mpr (word_emod W n)).trans hword
      simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using hh, hemodSpace⟩
  have hkeyN : key i ≤ valueBound W n := by unfold valueBound; nlinarith
  have hmulN : 2 ^ W * right i ≤ valueBound W n := by unfold key pairKey at hkeyN; omega
  have hprodN : key i * (n + 1) ≤ valueBound W n := by unfold threshold at hthreshold; omega
  have hmulZ : ((2 ^ W : ℕ) : ℤ) * (right i : ℤ) ≤ lim.word :=
    (by exact_mod_cast hmulN : ((2 ^ W : ℕ) : ℤ) * (right i : ℤ) ≤ (valueBound W n : ℤ)).trans hUword
  have hkeyZ : (left i : ℤ) + ((2 ^ W : ℕ) : ℤ) * (right i : ℤ) ≤ lim.word :=
    (by exact_mod_cast hkeyN : (left i : ℤ) + ((2 ^ W : ℕ) : ℤ) * (right i : ℤ) ≤ (valueBound W n : ℤ)).trans hUword
  have hprodZ : ((left i : ℤ) + ((2 ^ W : ℕ) : ℤ) * (right i : ℤ)) * ((n : ℤ) + 1) ≤ lim.word :=
    (by exact_mod_cast hprodN :
          ((left i : ℤ) + ((2 ^ W : ℕ) : ℤ) * (right i : ℤ)) * ((n : ℤ) + 1) ≤ (valueBound W n : ℤ)).trans
      hUword
  have hmul0 : 0 ≤ ((2 ^ W : ℕ) : ℤ) * (right i : ℤ) := by positivity
  have hprod0 : 0 ≤ ((left i : ℤ) + ((2 ^ W : ℕ) : ℤ) * (right i : ℤ)) * ((n : ℤ) + 1) := by positivity
  have hthZ : ((left i : ℤ) + ((2 ^ W : ℕ) : ℤ) * (right i : ℤ)) * ((n : ℤ) + 1) + (n : ℤ) ≤ lim.word := by
    simpa only [threshold, key, pairKey, Nat.cast_add, Nat.cast_mul, Nat.cast_one] using hthWord
  simp only [Nat.cast_pow, Nat.cast_ofNat] at hmulZ hkeyZ hprodZ hmul0 hprod0 hthZ
  have hhit := upperBound_hit hi hunique hperm hsorted
  change 0 < K ∧ K ≤ n ∧ S.getD (K - 1) 0 = (packed key n i : ℤ) at hhit
  have hnWidth : n < 2 ^ (2 * W + 1) :=
    by
    have hp : 0 < 2 ^ (2 * W) := Nat.two_pow_pos _
    rw [pow_succ]
    omega
  apply Meets.of_body (p := 3) (by rfl : program[3]? = some (body 0 1 2))
  unfold body time
  have hp :=
    powTable_meets (P := program) (p := 0) (d := d + 1) (μ := μ) (dst := work) (L := 2 * W + 2) (b := 2) rfl hw
      hpowSpace hpowBound
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
    | refine _root_.Light.Ends.callToThen (hp _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hp ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, powTableTime, LightBandLookup.searchTime]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [powTableTime, LightBandLookup.searchTime] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, powTableTime, LightBandLookup.searchTime] <;> omega)
    on_goal -1 => (rintro powRet μ₁ ⟨hpowers, hkeepPowers⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hPowers : Powers μ₁ work (2 * W + 1) := powers_of_segment hpowers
  have hradius := hPowers W (by omega)
  have hradiusN : μ₁ (work + W) = ((2 ^ W : ℕ) : ℤ) := by simpa using hradius
  have hradiusWord := hpowBound W (by omega)
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    refine _root_.Light.Ends.setToThen (2 ^ W : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hradius, hradiusN, powTableTime,
            LightBandLookup.searchTime]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hradius, hradiusN, powTableTime, LightBandLookup.searchTime] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hradius, hradiusN, powTableTime,
            LightBandLookup.searchTime] <;> omega)
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
    refine _root_.Light.Ends.setToThen (threshold : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, threshold, key, pairKey, powTableTime,
            LightBandLookup.searchTime]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [threshold, key, pairKey, powTableTime, LightBandLookup.searchTime] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, threshold, key, pairKey, powTableTime,
            LightBandLookup.searchTime] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  have hread : ∀ j < n, μ₁ (src + j) = S.getD j 0 := by
    intro j hj
    exact (hkeepPowers _ (Or.inl (by omega))).trans (hseg.getD (by omega) 0)
  have hsort : ∀ a b, a ≤ b → b < n → S.getD a 0 ≤ S.getD b 0 := by simpa only [hlen] using sorted_getD_le hsorted
  have hsearch :=
    LightBandLookup.search_meets (P := program) (pSearch := 1) (a := src) (n := n) (powers := work) (W := 2 * W + 1)
      (x := (threshold : ℤ)) rfl μ₁ (fun j => S.getD j 0) K hw (hsrc.trans (by omega)) (by omega) hsearchWord hread
      hPowers (BinarySearch.upperBound_correct _ _ _ hsort) (2 * W + 1) 0 le_rfl (by omega) (by omega) (d + 1)
      (by omega)
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
    | refine _root_.Light.Ends.callToThen (hsearch _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hsearch ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, threshold, powTableTime,
            LightBandLookup.searchTime]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [threshold, powTableTime, LightBandLookup.searchTime] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, threshold, powTableTime,
            LightBandLookup.searchTime] <;> omega)
    on_goal -1 => (rintro found μ₂ ⟨hfound, hmem⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  subst μ₂
  have hreadHit : μ₁ (src + (K - 1)) = (packed key n i : ℤ) := (hread _ (by omega)).trans hhit.2.2
  have hreadHitZ : μ₁ (((src : ℤ) + (K : ℤ) - 1).toNat) = (packed key n i : ℤ) :=
    by
    have ha : ((src : ℤ) + (K : ℤ) - 1).toNat = src + (K - 1) := by omega
    rw [ha]
    exact hreadHit
  have hreadHitSub : μ₁ (src + K - 1) = (packed key n i : ℤ) :=
    by
    have ha : src + K - 1 = src + (K - 1) := by omega
    rw [ha]
    exact hreadHit
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    refine _root_.Light.Ends.setToThen (packed key n i : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hfound, hreadHit, hreadHitZ, hreadHitSub,
            powTableTime, LightBandLookup.searchTime]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hfound, hreadHit, hreadHitZ, hreadHitSub, powTableTime, LightBandLookup.searchTime] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hfound, hreadHit, hreadHitZ, hreadHitSub,
            powTableTime, LightBandLookup.searchTime] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  have hem :=
    emod_meets (P := program) (p := 2) (d := d + 1) (μ := μ₁) (x := (packed key n i : ℤ)) rfl hEmod
      (by simpa only [Int.abs_natCast] using (Int.ofNat_le.mpr hcode.le))
  have hemTime : emodTime (packed key n i : ℤ).natAbs (n + 1) ≤ 100 * (Nat.log 2 (valueBound W n + 1) + 2) :=
    by
    have hh := emodRounds_le (M := n + 1) hcode.le
    simpa only [Int.natAbs_natCast, emodTime] using
      (show 43 * emodRounds (packed key n i) (n + 1) + 34 ≤ 100 * (Nat.log 2 (valueBound W n + 1) + 2) by omega)
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
    | refine _root_.Light.Ends.callToThen ((hem.mono_time hemTime) _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen (hem.mono_time hemTime) ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, powTableTime, LightBandLookup.searchTime]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [powTableTime, LightBandLookup.searchTime] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, powTableTime, LightBandLookup.searchTime] <;> omega)
    on_goal -1 => (rintro index μ₃ ⟨hindex, hkeepEmod⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  refine ⟨hindex.trans (packed_emod hi), ?_⟩
  intro j hj
  exact (hkeepEmod j hj).trans (hkeepPowers j (Or.inl hj))
end ThreeSum.LightReportingCatalogLookup

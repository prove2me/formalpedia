-- Prove2me | solution 1 for ThreeSum.LightReportingCatalogBatch.program_meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T16:51:52.152841+00:00
-- url     : https://prove2.me/submissions/ecc1b874-8cc3-43d9-823a-eb0a377bbc61

import Definitions.Def_Submission_ThreeSum_LightReportingCatalogQuery
import Definitions.Def_Submission_ThreeSum_ReportingHostSuffixValueBounds
import Definitions.Def_Submission_ThreeSum_LightReportingCatalogBatch
import Theorems.Thm_Light_Ends_append
import Theorems.Thm_Light_Exec_append
import Theorems.Thm_Light_LocalsBut_update
import Theorems.Thm_Light_Meets_append
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_SameOn_refl
import Theorems.Thm_Light_SameOutside2_refl
import Theorems.Thm_Light_SameOutside_refl
import Theorems.Thm_Light_frame_append_zeros
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSumApsp_AbsLe_append
import Theorems.Thm_ThreeSum_Arithmetic_missWeight_zero
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
import Theorems.Thm_ThreeSum_LightBandLookup_program_meets
import Theorems.Thm_ThreeSum_LightBlockBoxes_program_meets
import Theorems.Thm_ThreeSum_LightBlockQuery_program_meets
import Theorems.Thm_ThreeSum_LightBoxStages_program_meets
import Theorems.Thm_ThreeSum_LightBoxSum_partialSum_length
import Theorems.Thm_ThreeSum_LightBoxSum_program_meets
import Theorems.Thm_ThreeSum_LightCanonicalBoxSum_program_meets
import Theorems.Thm_ThreeSum_LightDownsetAddress_program_meets
import Theorems.Thm_ThreeSum_LightDownsetSize_program_meets
import Theorems.Thm_ThreeSum_LightExplicitSum_program_meets
import Theorems.Thm_ThreeSum_LightLeafSum_partialSum_length
import Theorems.Thm_ThreeSum_LightLeafSum_program_meets
import Theorems.Thm_ThreeSum_LightMaskErase_program_meets
import Theorems.Thm_ThreeSum_LightMaskMinimum_program_meets
import Theorems.Thm_ThreeSum_LightMaskUnion_program_meets
import Theorems.Thm_ThreeSum_LightQueryBox_program_meets
import Theorems.Thm_ThreeSum_LightQueryEnumeration_program_meets
import Theorems.Thm_ThreeSum_LightQueryWeights_program_meets
import Theorems.Thm_ThreeSum_LightRadixKeys_program_meets
import Theorems.Thm_ThreeSum_LightRadixRows_program_meets
import Theorems.Thm_ThreeSum_LightReportingAffine_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_bb907f0b533f0452
import Definitions.Def_WeightedCache3SUM_Alias_7f1c96094f5b1c13
import Definitions.Def_WeightedCache3SUM_Alias_00b35c3259394183
import Theorems.Thm_ThreeSum_LightReportingPackKeys_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_8a2cd73670b38080
import Definitions.Def_WeightedCache3SUM_Alias_f4a3749c14d0f5f9
import Definitions.Def_WeightedCache3SUM_Alias_a2387e9e7b890e99
import Definitions.Def_WeightedCache3SUM_Alias_a02564c7d1f1443e
import Theorems.Thm_ThreeSum_LightReportingSuffixBoxes_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_1d08961f6f3268cd
import Definitions.Def_WeightedCache3SUM_Alias_b15542bf609bcf98
import Theorems.Thm_ThreeSum_LightReportingSuffixLower_scanMask_all
import Theorems.Thm_ThreeSum_LightReportingSuffixLower_scanMask_zero
import Definitions.Def_WeightedCache3SUM_Alias_362a3b2d8940306a
import Definitions.Def_WeightedCache3SUM_Alias_40e937d67ef507b4
import Definitions.Def_WeightedCache3SUM_Alias_dfc7d85d435022ae
import Definitions.Def_WeightedCache3SUM_Alias_c19df7a51d8d0351
import Theorems.Thm_ThreeSum_LightReportingSuffixSum_partialSum_length
import Theorems.Thm_ThreeSum_LightSign_program_meets
import Theorems.Thm_ThreeSum_LightSignedBoxSetup_program_meets
import Theorems.Thm_ThreeSum_LightSignedLeafBatch_storedThrough_of_on
import Theorems.Thm_ThreeSum_LightSignedLeafGeneral_program_meets
import Theorems.Thm_ThreeSum_LightSignedLeafTable_program_meets
import Theorems.Thm_ThreeSum_LightSignedLeaf_program_meets
import Theorems.Thm_ThreeSum_LightSparseQuery_program_meets
import Theorems.Thm_ThreeSum_LightStageLookup_program_meets
import Theorems.Thm_ThreeSum_LightSubsetEnumerationSetup_program_meets
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_output_length
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_output_zero
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_program_meets
import Theorems.Thm_ThreeSum_LightSubsetSetup_program_meets
import Theorems.Thm_ThreeSum_LightWeightedEnumeration_output_length
import Theorems.Thm_ThreeSum_LightWeightedEnumeration_output_zero
import Theorems.Thm_ThreeSum_LightWeightedEnumeration_program_meets
import Theorems.Thm_ThreeSum_LightWeightedEnumeration_total_succ
import Theorems.Thm_ThreeSum_LightWeightedEnumeration_total_zero
import Theorems.Thm_ThreeSum_LightZetaCell_program_meets
import Theorems.Thm_ThreeSum_LightZetaPass_program_meets
import Theorems.Thm_ThreeSum_LightZetaStages_program_meets
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
import Theorems.Thm_ThreeSum_ReportingHostCatalogSelection_selected_box_end
import Theorems.Thm_ThreeSum_ReportingHostPackedCatalog_codes_length
import Theorems.Thm_ThreeSum_ReportingHostPairSegments_leftMasks_length
import Theorems.Thm_ThreeSum_ReportingHostPairSegments_program_meets
import Theorems.Thm_ThreeSum_ReportingHostPairSegments_rightMasks_length
import Theorems.Thm_ThreeSum_ReportingHostQueryBounds_boxStored_of_on
import Definitions.Def_WeightedCache3SUM_Alias_e67693721710fb34
import Theorems.Thm_ThreeSum_ReportingHostSuffix_liftSet_card
import Theorems.Thm_ThreeSum_ReportingHostSuffix_liftSet_empty
import Theorems.Thm_ThreeSum_ReportingHostSuffix_mem_lowerSet
import Theorems.Thm_ThreeSum_ReportingHostSuffix_shiftEmbedding_val
import Theorems.Thm_ThreeSum_SignedLeaf_mem_explicitMissing
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_zero
import Theorems.Thm_ThreeSum_SubsetAddress_natPositions_card
import Theorems.Thm_ThreeSum_SubsetAddress_subsetMask_isMask
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
attribute [local simp] ThreeSum.LightReportingSuffixLower.scanMask_all
attribute [local simp] ThreeSum.LightReportingSuffixLower.scanMask_zero
attribute [local simp] ThreeSum.LightReportingSuffixSum.partialSum_length
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
open ThreeSum ThreeSum.LightReportingCatalogBatch
open Light Finset ThreeSum.SubsetAddress ThreeSum.LightPascal
open BlockRows BlockForced BlockEncoding BlockIndexedQuery StoredReporting
open GlobalEncoding LocalCoverBounds RawIncidences RawReporting RawPrefixCounts LightBlockQuery
open ReportingHostSuffix ReportingHostPrefixOrder LightReportingPrefixCatalog LightReportingSuffixCatalog
set_option maxHeartbeats 2200000
set_option maxRecDepth 8000
variable {lim : Limits}
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ] [DecidableEq α] [DecidableEq β] [DecidableEq γ]
namespace ThreeSum.LightReportingCatalogBatch
theorem _root_.solution {μ : ℕ → ℤ}
    {h J k t baseL baseR boxCut boxBase indexBase ptrBase inL inR n dst maskBase work depth : ℕ} (pMod shift : ℤ)
    (A : Finset α) (B : Finset β) (C : Finset γ) (a : α → ℤ) (b : β → ℤ) (c : γ → ℤ) (w : Wanted h J α)
    (pres : ℕ → List (Finset (Fin (512 * h)))) (hk : k ≤ J) (hp : ∀ i < n, ValidPrefix w.2.2 k (pres i))
    (hkey : w.1 ∈ A ∧ globalModulus h J ∣ (a w.1 % pMod + lift w.2.1 * pMod + shift) - globalKey w.2.2)
    (hw : (lim.space : ℤ) ≤ lim.word) (hdataL : baseL + (width h J + 1) * downsetCap (width h J) (sourceCut h J) ≤ dst)
    (hdataR : baseR + (width h J + 1) * downsetCap (width h J) (sourceCut h J) ≤ dst)
    (hindex : indexBase + count h k ≤ dst) (hptr : ptrBase + count h k ≤ dst)
    (hboxesEnd : boxBase + count h k * stride (suffixStage J (512 * h) k) boxCut ≤ dst) (hinL : inL + n ≤ dst)
    (hinR : inR + n ≤ dst) (hdst : dst + n ≤ maskBase)
    (hmasks : maskBase + LightSparseQuery.queryItems (residualSize h J k) t ≤ work)
    (hspace : work + 1 + tableSize (width h J) + (width h J + 1) ≤ lim.space)
    (hpowSpace : work + (2 * width h J + 2) ≤ lim.space)
    (hemodSpace :
      work + (Nat.log 2 (LightReportingCatalogLookup.valueBound (width h J) (count h k) + 1) + 2) ≤ lim.space)
    (hword : (((width h J + 1) * 2 ^ (width h J + 1) : ℕ) : ℤ) ≤ lim.word)
    (hlookupWord : (LightReportingCatalogLookup.word (width h J) (count h k) : ℤ) ≤ lim.word)
    (hvalueWord :
      (LightSparseQuery.magnitudeBound (suffixStage J (512 * h) k) (suffixStage J (512 * h) k) (residualSize h J k) t
            B.card C.card :
          ℤ) ≤
        lim.word)
    (ht : t ≤ residualSize h J k + 1) (hboxCut : boxCut ≤ residualSize h J k) (hflags : residualSize h J k - t ≤ boxCut)
    (hstoredL : LightZetaStages.StoredThrough μ baseL (sourceCut h J) (leftSource pMod B b w.2.2) (width h J))
    (hstoredR : LightZetaStages.StoredThrough μ baseR (sourceCut h J) (rightSource pMod shift C c w.2.2) (width h J))
    (hindexData :
      ∃ S : List ℤ,
        Seg μ indexBase S ∧
          S.Perm (ReportingHostPackedCatalog.codes (ReportingHostPackedCatalog.prefixKey h J k) (count h k)) ∧
            S.Pairwise (· ≤ ·))
    (hptrs :
      SegN μ ptrBase (List.ofFn fun i : Fin (count h k) => boxBase + i.val * stride (suffixStage J (512 * h) k) boxCut))
    (hboxes :
      ∀ i < count h k,
        LightBoxStages.StoredThrough μ (boxBase + i * stride (suffixStage J (512 * h) k) boxCut) boxCut
          (leafWeight (block_fit hk) (leftSource pMod B b w.2.2) (rightSource pMod shift C c w.2.2)
            (suffixStage J (512 * h) k) (preL h J k i) (preR h J k i))
          (suffixStage J (512 * h) k))
    (hreadL : ∀ i < n, μ (inL + i) = (subsetMask (leftPrefix k (prefixRows (J := J) (pres i))) : ℤ))
    (hreadR : ∀ i < n, μ (inR + i) = (subsetMask (rightPrefix k (outputRows w.2.2) (prefixRows (J := J) (pres i))) : ℤ))
    (hd : depth + 2 * width h J + 13 ≤ lim.depth) :
    Meets lim program 36 depth
      [width h J, sourceCut h J, suffixStage J (512 * h) k, k * h, k * h, suffixStage J (512 * h) k, k * (512 * h),
        residualSize h J k, subsetMask (querySet k (outputRows w.2.2)), t, baseL, baseR, boxCut, indexBase, ptrBase,
        count h k, inL, inR, n, dst, maskBase, work]
      μ (time h J k t n)
      (fun _ μ' =>
        SegN μ' dst
            (List.ofFn fun i : Fin n => prefixQuery (rawOn h J pMod shift (A ×ˢ (B ×ˢ C)) a b c) w k (pres i.val)) ∧
          KeptBut μ μ' maskBase dst n) :=
  by
  let counts := fun i => prefixQuery (rawOn h J pMod shift (A ×ˢ (B ×ˢ C)) a b c) w k (pres i)
  obtain ⟨S, hseg, hperm, hsorted⟩ := hindexData
  have hlen : S.length = count h k := hperm.length_eq.trans (ReportingHostPackedCatalog.codes_length _ _)
  have hmask (U : Finset (Fin (width h J))) : (subsetMask U : ℤ) ≤ lim.word :=
    by
    have hpow : (2 ^ (width h J) : ℕ) ≤ (width h J + 1) * 2 ^ (width h J + 1) :=
      (Nat.pow_le_pow_right (by decide) (by omega)).trans (Nat.le_mul_of_pos_left _ (by omega))
    exact (Int.ofNat_le.mpr ((subsetMask_isMask U).1.le.trans hpow)).trans hword
  apply Meets.of_body (p := 36) (by rfl : program[36]? = some (body 35))
  unfold body time
  refine
    Ends.for (lim := lim) (P := program) (d := depth) (i := 22) (hi := v 18) (body := roundBody 35)
      (Inv μ counts h J k t (subsetMask (querySet k (outputRows w.2.2))) baseL baseR boxCut indexBase ptrBase inL inR n
        dst maskBase work)
      n (LightReportingCatalogQuery.time h J k t + 150) ?start ?round ?done ?bound (hT := by
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
            | (ring_nf; omega)))
  case start =>
    refine ⟨0, 0, 0, μ, ?_, by simp, SameOn.refl⟩
    simp [update_frame_setLocal]
    change
      frame
          ([(width h J : ℤ), sourceCut h J, suffixStage J (512 * h) k, k * h, k * h, suffixStage J (512 * h) k,
            k * (512 * h), residualSize h J k, subsetMask (querySet k (outputRows w.2.2)), t, baseL, baseR, boxCut,
            indexBase, ptrBase, count h k, inL, inR, n, dst, maskBase, work, 0]) =
        frame
          ([(width h J : ℤ), sourceCut h J, suffixStage J (512 * h) k, k * h, k * h, suffixStage J (512 * h) k,
              k * (512 * h), residualSize h J k, subsetMask (querySet k (outputRows w.2.2)), t, baseL, baseR, boxCut,
              indexBase, ptrBase, count h k, inL, inR, n, dst, maskBase, work, 0] ++
            [0, 0, 0])
    exact (frame_append_zeros _ 3).symm
  case round =>
    rintro j _ hj _ ⟨left, right, result, μ', rfl, hout, hkeep⟩
    have hkread (z : ℕ) (hz : z < dst) : μ' z = μ z := hkeep z ⟨by omega, Or.inl hz⟩
    have hlread := (hkread (inL + j) (by omega)).trans (hreadL j hj)
    have hrread := (hkread (inR + j) (by omega)).trans (hreadR j hj)
    have hlword := hmask (leftPrefix k (prefixRows (J := J) (pres j)))
    have hrword := hmask (rightPrefix k (outputRows w.2.2) (prefixRows (J := J) (pres j)))
    have hsourceL :=
      LightSignedLeafBatch.storedThrough_of_on hstoredL (by intro z _ hz; exact hkread z (hz.trans_le hdataL))
    have hsourceR :=
      LightSignedLeafBatch.storedThrough_of_on hstoredR (by intro z _ hz; exact hkread z (hz.trans_le hdataR))
    have hindexData' :
      ∃ S : List ℤ,
        Seg μ' indexBase S ∧
          S.Perm (ReportingHostPackedCatalog.codes (ReportingHostPackedCatalog.prefixKey h J k) (count h k)) ∧
            S.Pairwise (· ≤ ·) :=
      by
      refine ⟨S, ?_, hperm, hsorted⟩
      intro z hz
      exact (hkread _ (by rw [hlen] at hz; omega)).trans (hseg z hz)
    have hptrs' :
      SegN μ' ptrBase
        (List.ofFn fun i : Fin (count h k) => boxBase + i.val * stride (suffixStage J (512 * h) k) boxCut) :=
      by
      intro z hz
      have hz' : z < count h k := by simpa only [List.length_map, List.length_ofFn] using hz
      exact (hkread _ (by omega)).trans (hptrs z hz)
    have hboxes' (z : ℕ) (hz : z < count h k) :=
      ReportingHostQueryBounds.boxStored_of_on (hboxes z hz)
        (by
          intro u _ hu
          exact hkread u (hu.trans_le (ReportingHostCatalogSelection.selected_box_end hz hboxesEnd)))
    have hv :=
      ReportingHostSuffixValueBounds.prefix_count_le_word pMod shift A B C a b c w (pres j) hk (hp j hj) hkey hvalueWord
    change (counts j : ℤ) ≤ lim.word at hv
    unfold roundBody
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        (repeat
            with_unfolding_none
              first
              | refine _root_.Light.Ends.seqAssoc ?_
              | refine _root_.Light.Ends.skipThen ?_))
      refine _root_.Light.Ends.setToThen (subsetMask (leftPrefix k (prefixRows (J := J) (pres j))) : ℕ) ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hlread,
              LightReportingCatalogQuery.time]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [hlread, LightReportingCatalogQuery.time] <;> first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hlread, LightReportingCatalogQuery.time] <;> omega)
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
      refine
        _root_.Light.Ends.setToThen (subsetMask (rightPrefix k (outputRows w.2.2) (prefixRows (J := J) (pres j))) : ℕ)
          ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hrread,
              LightReportingCatalogQuery.time]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [hrread, LightReportingCatalogQuery.time] <;> first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hrread, LightReportingCatalogQuery.time] <;> omega)
      try with_unfolding_none refine _root_.Light.Ends.skip ?_
    have hquery :=
      (LightReportingCatalogQuery.program_meets (depth := depth + 1) (μ := μ') pMod shift A B C a b c w (pres j) hk
            (hp j hj) hkey hw (by omega) (by omega) (by omega) (by omega) (by omega) hmasks hspace hpowSpace hemodSpace
            hword hlookupWord hvalueWord ht hboxCut hflags hsourceL hsourceR hindexData' hptrs' hboxes'
            (by omega)).append
        [body 35]
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
      | refine _root_.Light.Ends.callToThen (hquery _ (by omega)) ?_ ?_ ?_ ?_
      | refine _root_.Light.Ends.callToThen hquery ?_ ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil,
              LightReportingCatalogQuery.time]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [LightReportingCatalogQuery.time] <;> first
              | omega
              | (ring_nf; omega))
      on_goal -1 => omega
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightReportingCatalogQuery.time] <;> omega)
      on_goal -1 => (rintro value ν ⟨hvalue, hkeepQ⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
    change value = (counts j : ℤ) at hvalue
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        (repeat
            with_unfolding_none
              first
              | refine _root_.Light.Ends.seqAssoc ?_
              | refine _root_.Light.Ends.skipThen ?_))
      refine _root_.Light.Ends.storeToThen (dst + j) (counts j : ℤ) ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hvalue,
              LightReportingCatalogQuery.time]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [hvalue, LightReportingCatalogQuery.time] <;> first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hvalue, LightReportingCatalogQuery.time] <;> omega)
      try with_unfolding_none refine _root_.Light.Ends.skip ?_
    refine
      ⟨by simp, (subsetMask (leftPrefix k (prefixRows (J := J) (pres j))) : ℤ),
        (subsetMask (rightPrefix k (outputRows w.2.2) (prefixRows (J := J) (pres j))) : ℤ), value,
        Function.update ν (dst + j) (counts j : ℤ), ?_, ?_, ?_⟩
    · simp [update_frame_setLocal]
    · intro z hz
      by_cases he : z = j
      · subst z; simp
      · have hzj : z < j := by omega
        rw [Function.update_of_ne (by omega), hkeepQ (dst + z) ⟨by omega, Or.inl (by omega)⟩]
        exact hout z hzj
    · intro z hz
      rw [Function.update_of_ne (by rcases hz.2 with h | h <;> omega)]
      exact (hkeepQ z ⟨by omega, Or.inl hz.1⟩).trans (hkeep z hz)
  case done =>
    rintro _ _ ⟨left, right, result, μ', rfl, hout, hkeep⟩
    refine ⟨?_, hkeep⟩
    intro j hj
    have hj' : j < n := by simpa only [List.length_map, List.length_ofFn] using hj
    have hh := hout j hj'
    simpa only [List.getElem_map, List.getElem_ofFn] using hh
  case bound =>
    rintro j _ hj _ ⟨left, right, result, μ', rfl, _, _⟩
    ( (try have := _root_.Light.Std.space_le (by assumption))
      (try have := _root_.Light.Std.const_le (by assumption))
      simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
end ThreeSum.LightReportingCatalogBatch

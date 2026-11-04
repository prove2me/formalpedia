-- Prove2me | solution 1 for ThreeSum.SourceFiniteData.Normalized.keep_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:13:03.355196+00:00
-- url     : https://prove2.me/submissions/d4703870-58c4-4a36-b07e-50b3f8f2991b

import Definitions.Def_Submission_ThreeSum_SourceFiniteData
import Definitions.Def_Submission_ThreeSum_SourceFiniteRetention
import Theorems.Thm_Light_MatAt_keep
import Theorems.Thm_Light_SegN_keep
import Theorems.Thm_Light_Seg_keep
import Theorems.Thm_Light_Seg_of_kept
import Theorems.Thm_Light_VecAt_keep
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_Arithmetic_missWeight_zero
import Theorems.Thm_ThreeSum_BandCandidateRows_cells_length
import Theorems.Thm_ThreeSum_BandCandidateRows_records_length
import Theorems.Thm_ThreeSum_BandPartition_size_mono
import Theorems.Thm_ThreeSum_BandRawA_Stored_of_kept
import Theorems.Thm_ThreeSum_BandRawA_count_mono
import Theorems.Thm_ThreeSum_BandRawA_count_zero
import Theorems.Thm_ThreeSum_BandRawA_firstRows_zero
import Theorems.Thm_ThreeSum_BandRawA_items_length_le
import Theorems.Thm_ThreeSum_BandRawA_mem_finiteAIndices
import Theorems.Thm_ThreeSum_BandRawA_mem_finiteAllProducts
import Theorems.Thm_ThreeSum_BandRawA_mem_finiteBandPositions
import Theorems.Thm_ThreeSum_BandRawA_mem_finiteOwnerProduct
import Theorems.Thm_ThreeSum_BandWeightedScore_partialScore_zero
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
import Definitions.Def_WeightedCache3SUM_Alias_00da40658bb1c003
import Theorems.Thm_ThreeSum_BlockSourceEncoding_modulus_cast
import Theorems.Thm_ThreeSum_BlockSourceFlags_candidateIndices_fin
import Theorems.Thm_ThreeSum_BlockSourceOccurrenceOrder_outputOccurrences_representative
import Theorems.Thm_ThreeSum_BoxStages_mem_prefix
import Theorems.Thm_ThreeSum_BoxStages_prefix_all
import Theorems.Thm_ThreeSum_BoxStages_prefix_zero
import Theorems.Thm_ThreeSum_BoxStages_stageValue_all
import Theorems.Thm_ThreeSum_BoxStages_stageValue_zero
import Theorems.Thm_ThreeSum_ColorClassLists_value_fin
import Theorems.Thm_ThreeSum_CyclicFold_asPolynomial_replicate_zero
import Theorems.Thm_ThreeSum_ExplicitLayers_leaves_length
import Theorems.Thm_ThreeSum_ExplicitLayers_missing_length
import Theorems.Thm_ThreeSum_ExplicitLayers_valueSum_zero
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
import Theorems.Thm_ThreeSum_LightBandEnumeration_At_keep
import Theorems.Thm_ThreeSum_LightBandEnumeration_count_mono
import Definitions.Def_WeightedCache3SUM_Alias_a6ca635f54b46105
import Definitions.Def_WeightedCache3SUM_Alias_162bee3568c215d0
import Theorems.Thm_ThreeSum_LightBoxSum_partialSum_length
import Theorems.Thm_ThreeSum_LightClassFilter_items_length_le
import Theorems.Thm_ThreeSum_LightClassFilter_items_zero
import Definitions.Def_WeightedCache3SUM_Alias_7dc97c785b0d6c4c
import Theorems.Thm_ThreeSum_LightHistogram_count_zero
import Theorems.Thm_ThreeSum_LightKaratsuba_ProductAt_bound
import Theorems.Thm_ThreeSum_LightKaratsuba_window_sub
import Theorems.Thm_ThreeSum_LightLeafSum_partialSum_length
import Definitions.Def_WeightedCache3SUM_Alias_82db098e10427a83
import Theorems.Thm_ThreeSum_LightSortedBands_Prepared_keep
import Theorems.Thm_ThreeSum_LightSourceRowScan_count_zero
import Theorems.Thm_ThreeSum_LightSourceRowScan_hash_zero
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
import Theorems.Thm_ThreeSum_RawAKeyLists_records_length
import Theorems.Thm_ThreeSum_ReportingHostSuffix_liftSet_card
import Theorems.Thm_ThreeSum_ReportingHostSuffix_liftSet_empty
import Theorems.Thm_ThreeSum_ReportingHostSuffix_mem_lowerSet
import Theorems.Thm_ThreeSum_ReportingHostSuffix_shiftEmbedding_val
import Theorems.Thm_ThreeSum_SignedLeaf_mem_explicitMissing
import Definitions.Def_WeightedCache3SUM_Alias_470e48753c64c7fc
import Theorems.Thm_ThreeSum_SourceBandBankLayout_At_of_kept
import Theorems.Thm_ThreeSum_SourceBandData_At_of_kept
import Definitions.Def_WeightedCache3SUM_Alias_78e5c19e1b3827d6
import Theorems.Thm_ThreeSum_SourceBuckets_count_mono
import Theorems.Thm_ThreeSum_SourceBuckets_offset_zero
import Theorems.Thm_ThreeSum_SourceFlagProduct_product_zero
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
import Theorems.Thm_ThreeSum_Switch_mem_candidates
import Theorems.Thm_ThreeSum_WantedPairs_cells_length
import Theorems.Thm_ThreeSum_WantedPairs_count_mono
import Theorems.Thm_ThreeSum_WantedPairs_count_zero
import Theorems.Thm_ThreeSum_WantedPairs_pairs_zero
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
attribute [local simp] ThreeSum.BandRawA.count_zero
attribute [local simp] ThreeSum.BandRawA.firstRows_zero
attribute [local simp] ThreeSum.BandRawA.mem_finiteAIndices
attribute [local simp] ThreeSum.BandRawA.mem_finiteAllProducts
attribute [local simp] ThreeSum.BandRawA.mem_finiteBandPositions
attribute [local simp] ThreeSum.BandRawA.mem_finiteOwnerProduct
attribute [local simp] ThreeSum.BandWeightedScore.partialScore_zero
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
attribute [local simp] ThreeSum.BlockSourceFlags.candidateIndices_fin
attribute [local simp] ThreeSum.BlockSourceOccurrenceOrder.outputOccurrences_representative
attribute [local simp] ThreeSum.BoxStages.mem_prefix
attribute [local simp] ThreeSum.BoxStages.prefix_all
attribute [local simp] ThreeSum.BoxStages.prefix_zero
attribute [local simp] ThreeSum.BoxStages.stageValue_all
attribute [local simp] ThreeSum.BoxStages.stageValue_zero
attribute [local simp] ThreeSum.ColorClassLists.value_fin
attribute [local simp] ThreeSum.CyclicFold.asPolynomial_replicate_zero
attribute [local simp] ThreeSum.ExplicitLayers.leaves_length
attribute [local simp] ThreeSum.ExplicitLayers.missing_length
attribute [local simp] ThreeSum.ExplicitLayers.valueSum_zero
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
attribute [local simp] ThreeSum.LightBoxSum.partialSum_length
attribute [local simp] ThreeSum.LightClassFilter.items_zero
attribute [local simp] ThreeSum.LightHistogram.count_zero
attribute [local simp] ThreeSum.LightKaratsuba.window_sub
attribute [local simp] ThreeSum.LightLeafSum.partialSum_length
attribute [local simp] ThreeSum.LightSourceRowScan.count_zero
attribute [local simp] ThreeSum.LightSourceRowScan.hash_zero
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
attribute [local simp] ThreeSum.ReportingHostSuffix.liftSet_card
attribute [local simp] ThreeSum.ReportingHostSuffix.liftSet_empty
attribute [local simp] ThreeSum.ReportingHostSuffix.mem_lowerSet
attribute [local simp] ThreeSum.ReportingHostSuffix.shiftEmbedding_val
attribute [local simp] ThreeSum.SignedLeaf.mem_explicitMissing
attribute [local simp] ThreeSum.SourceBuckets.offset_zero
attribute [local simp] ThreeSum.SourceFlagProduct.product_zero
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
attribute [local simp] ThreeSum.Switch.mem_candidates
attribute [local simp] ThreeSum.WantedPairs.count_zero
attribute [local simp] ThreeSum.WantedPairs.pairs_zero
attribute [local simp] ThreeSum.WeightedScore.corrections_zero
attribute [local simp] ThreeSum.WeightedScore.remaining_zero



set_option autoImplicit false
open ThreeSum ThreeSum.SourceFiniteData
open Light BandPartition BandCandidateRows BandRawA
namespace ThreeSum.SourceFiniteData
namespace Normalized
theorem _root_.solution {μ ν : ℕ → ℤ} {av ae bv be cv ce tables rec vals g n bound : ℕ}
    {hg : 0 < g} {originalA originalB originalC A B C : List ℤ}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)} {r : ℤ}
    (H : Normalized μ av ae bv be cv ce tables rec vals g hg originalA originalB originalC A B C hsA hsB hsC r)
    (hk : Kept μ ν bound)
    (hA : originalA.length ≤ n) (hB : originalB.length ≤ n) (hC : originalC.length ≤ n)
    (hav : av+n ≤ bound) (hae : ae+2+2*n ≤ bound)
    (hbv : bv+n ≤ bound) (hbe : be+2+2*n ≤ bound)
    (hcv : cv+n ≤ bound) (hce : ce+2+2*n ≤ bound)
    (htables : tables+ColorBandBounds.count n g ≤ bound)
    (hrecords : rec+4*ColorBandBounds.count n g ≤ bound)
    (hcatalog : LightBandRawA.space vals (ColorBandBounds.count n g) g ≤ bound) :
    Normalized ν av ae bv be cv ce tables rec vals g hg originalA originalB originalC A B C hsA hsB hsC r := by
  obtain ⟨hr,repA,repB,repC,tablesAt,recordRows,incidences⟩ := H
  have hnA := repA.2.1.trans hA
  have hnB := repB.2.1.trans hB
  have hnC := repC.2.1.trans hC
  let FA := family (fun i => A.getD i 0) A.length g hg (LightSortedBands.getD_strict hsA)
  let FB := family (fun i => B.getD i 0) B.length g hg (LightSortedBands.getD_strict hsB)
  let FC := family (fun i => C.getD i 0) C.length g hg (LightSortedBands.getD_strict hsC)
  let rs := sortedRecords A B C g hg hsA hsB hsC
  have ha : FA.size ≤ size n g := size_mono hnA
  have hb : FB.size ≤ size n g := size_mono hnB
  have hc : FC.size ≤ size n g := size_mono hnC
  have hcount : LightBandEnumeration.count FA.size FB.size FC.size ≤ ColorBandBounds.count n g := by
    have hm := LightBandEnumeration.count_mono ha hb hc
    have he : LightBandEnumeration.count (size n g) (size n g) (size n g)=ColorBandBounds.count n g := by
      unfold LightBandEnumeration.count ColorBandBounds.count
      ring
    rwa [he] at hm
  have hlen : rs.length ≤ ColorBandBounds.count n g := by
    simpa only [rs,sortedRecords,records_length,FA,FB,FC] using hcount
  have hitems : (items A.length g rs).length ≤ g*rs.length := items_length_le ..
  have hgc := Nat.mul_le_mul_left g hlen
  have hfour := Nat.mul_le_mul_left 4 hlen
  dsimp only [rs] at hitems hgc
  refine ⟨hr,repA.keep hk (by omega) (by omega),repB.keep hk (by omega) (by omega),
    repC.keep hk (by omega) (by omega),?_,?_,?_⟩
  · exact LightBandRawAColor.tables_keep tablesAt hk ((Nat.add_le_add_left hcount tables).trans htables)
  · exact recordRows.of_kept hk (by simpa only [cells_length] using (show rec+4*rs.length ≤ bound by omega))
  · apply incidences.of_kept hk
    all_goals
      change _ ≤ bound
      simp only [LightBandRawA.space,LightBandRawA.positionBase,LightBandRawA.ownerBase,LightBandRawA.capacity] at hcatalog ⊢
      omega
end Normalized
end ThreeSum.SourceFiniteData

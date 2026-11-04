-- Prove2me | solution 1 for ThreeSum.LightTernaryColorPrelude.meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T15:12:00.703975+00:00
-- url     : https://prove2.me/submissions/b16a8588-5c56-4df4-b1fc-0126e0ae3e3c

import Definitions.Def_Submission_ThreeSum_LightColorBands
import Definitions.Def_Submission_ThreeSum_LightColorParametersCosts
import Definitions.Def_Submission_ThreeSum_LightColorScanHost
import Definitions.Def_Submission_ThreeSum_LightTernaryColorPrelude
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Definitions.Def_WeightedCache3SUM_Alias_3f3326597d4f4ccd
import Theorems.Thm_Light_toNat_natCast_add_natCast
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
import Theorems.Thm_ThreeSum_ColorClassLists_length_classList_le
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
import Definitions.Def_WeightedCache3SUM_Alias_fe1d986d2522f297
import Definitions.Def_WeightedCache3SUM_Alias_4c62aff33317338c
import Definitions.Def_WeightedCache3SUM_Alias_d9563e39a04084e5
import Definitions.Def_WeightedCache3SUM_Alias_fecb00c51dea7534
import Definitions.Def_WeightedCache3SUM_Alias_ee0aafec5c99c3fa
import Definitions.Def_WeightedCache3SUM_Alias_f2e191e7f7b92ebc
import Theorems.Thm_ThreeSum_LightBlockQuery_meets
import Definitions.Def_WeightedCache3SUM_Alias_180c3abfd6d390ad
import Definitions.Def_WeightedCache3SUM_Alias_443601c744eb157d
import Theorems.Thm_ThreeSum_LightBoxSum_partialSum_length
import Definitions.Def_WeightedCache3SUM_Alias_84a6d1c69132a490
import Definitions.Def_WeightedCache3SUM_Alias_cd0e44d57dc54f82
import Theorems.Thm_ThreeSum_LightClassFilter_items_zero
import Definitions.Def_WeightedCache3SUM_Alias_98152438e5b788f3
import Definitions.Def_WeightedCache3SUM_Alias_ec1db2019105351a
import Definitions.Def_WeightedCache3SUM_Alias_e24e346b903ae22f
import Definitions.Def_WeightedCache3SUM_Alias_1bc522b5c56beb35
import Definitions.Def_WeightedCache3SUM_Alias_5d83a00a3f301eb9
import Theorems.Thm_ThreeSum_LightColorParametersCosts_width_sufficient
import Definitions.Def_WeightedCache3SUM_Alias_6cd6f72823a59258
import Definitions.Def_WeightedCache3SUM_Alias_84379a8b0e0ffbf1
import Definitions.Def_WeightedCache3SUM_Alias_9d1dcf23da3dbe87
import Definitions.Def_WeightedCache3SUM_Alias_673095557addf664
import Definitions.Def_WeightedCache3SUM_Alias_31257a44f822c74e
import Theorems.Thm_ThreeSum_LightExplicitSum_meets
import Definitions.Def_WeightedCache3SUM_Alias_3718d050d478b160
import Definitions.Def_WeightedCache3SUM_Alias_35c8db9f38e66e96
import Theorems.Thm_ThreeSum_LightHistogram_count_zero
import Definitions.Def_WeightedCache3SUM_Alias_54cf43efc96d8adf
import Theorems.Thm_ThreeSum_LightKaratsuba_window_sub
import Theorems.Thm_ThreeSum_LightLeafSum_meets
import Theorems.Thm_ThreeSum_LightLeafSum_partialSum_length
import Definitions.Def_WeightedCache3SUM_Alias_9f151fd16c06b1ef
import Definitions.Def_WeightedCache3SUM_Alias_e2ad5e59f3af6ab7
import Definitions.Def_WeightedCache3SUM_Alias_3252ff1ef14149f2
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Definitions.Def_WeightedCache3SUM_Alias_2ab790e73b946b9f
import Definitions.Def_WeightedCache3SUM_Alias_c287aeb916bf4368
import Definitions.Def_WeightedCache3SUM_Alias_e1d95931a2ead3e4
import Theorems.Thm_ThreeSum_LightModuloCounts_Procs_meets
import Definitions.Def_WeightedCache3SUM_Alias_03cdb09d18890d4e
import Definitions.Def_WeightedCache3SUM_Alias_d92129e9a4741fac
import Definitions.Def_WeightedCache3SUM_Alias_d98593d0ef804094
import Definitions.Def_WeightedCache3SUM_Alias_97fa2774a4e14663
import Theorems.Thm_ThreeSum_LightPrimality_Procs_meets
import Definitions.Def_WeightedCache3SUM_Alias_137b880911028d95
import Definitions.Def_WeightedCache3SUM_Alias_a00dee90c4e0ea45
import Definitions.Def_WeightedCache3SUM_Alias_e3ff37f6db941441
import Definitions.Def_WeightedCache3SUM_Alias_daea56ef26e5693b
import Definitions.Def_WeightedCache3SUM_Alias_874c626a95c648fa
import Definitions.Def_WeightedCache3SUM_Alias_4b4040d8de1fb856
import Definitions.Def_WeightedCache3SUM_Alias_32e47c9a32bb047b
import Theorems.Thm_ThreeSum_LightReportingAffine_meets
import Definitions.Def_WeightedCache3SUM_Alias_166ac700a68b6c71
import Definitions.Def_WeightedCache3SUM_Alias_7aba91d69ad782cd
import Definitions.Def_WeightedCache3SUM_Alias_4b224c9ee30c137c
import Definitions.Def_WeightedCache3SUM_Alias_dc0a334da481a327
import Definitions.Def_WeightedCache3SUM_Alias_9b3006da0fcbdf4e
import Theorems.Thm_ThreeSum_LightScales_Procs_meets
import Definitions.Def_WeightedCache3SUM_Alias_984013d7ba738e5d
import Definitions.Def_WeightedCache3SUM_Alias_276ab4baf5d9c1f3
import Definitions.Def_WeightedCache3SUM_Alias_3cbba57b9f47c556
import Theorems.Thm_ThreeSum_LightSignedBoxSetup_meets
import Theorems.Thm_ThreeSum_LightSignedLeafBatch_meets
import Theorems.Thm_ThreeSum_LightSignedLeafCell_meets
import Definitions.Def_WeightedCache3SUM_Alias_d9b8d9638683d951
import Theorems.Thm_ThreeSum_LightSignedLeafTable_meets
import Theorems.Thm_ThreeSum_LightSignedLeaf_meets
import Definitions.Def_WeightedCache3SUM_Alias_73246870e6a638ab
import Definitions.Def_WeightedCache3SUM_Alias_f253b70ba796e513
import Theorems.Thm_ThreeSum_LightSparseQuery_meets
import Definitions.Def_WeightedCache3SUM_Alias_5c1e55e66cf081b7
import Definitions.Def_WeightedCache3SUM_Alias_f29d07b5f5ce2e2c
import Definitions.Def_WeightedCache3SUM_Alias_098d503c7eb426c7
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_output_length
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_output_zero
import Definitions.Def_WeightedCache3SUM_Alias_037fdff845f4735d
import Definitions.Def_WeightedCache3SUM_Alias_8a94481881de516b
import Definitions.Def_WeightedCache3SUM_Alias_faf0bf412734022a
import Theorems.Thm_ThreeSum_LightWeightedEnumeration_output_length
import Theorems.Thm_ThreeSum_LightWeightedEnumeration_output_zero
import Theorems.Thm_ThreeSum_LightWeightedEnumeration_total_succ
import Theorems.Thm_ThreeSum_LightWeightedEnumeration_total_zero
import Definitions.Def_WeightedCache3SUM_Alias_c0e528b1e0cee255
import Definitions.Def_WeightedCache3SUM_Alias_44f02ed11cdb23f7
import Definitions.Def_WeightedCache3SUM_Alias_d110f06b53aa1a96
import Definitions.Def_WeightedCache3SUM_Alias_197272b1cee37ac5
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
import Theorems.Thm_ThreeSum_ReportingHostPairSegments_leftMasks_length
import Theorems.Thm_ThreeSum_ReportingHostPairSegments_rightMasks_length
import Theorems.Thm_ThreeSum_ReportingHostRelocation_meets
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
import Theorems.Thm_ThreeSum_Switch_mem_candidates
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
attribute [local simp] ThreeSum.Switch.mem_candidates
attribute [local simp] ThreeSum.WeightedScore.corrections_zero
attribute [local simp] ThreeSum.WeightedScore.remaining_zero
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryColorPrelude
open Light ColorClassLists LightColorParametersCosts
set_option maxHeartbeats 7000000
set_option maxRecDepth 20000
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightTernaryColorPrelude
theorem _root_.solution {pMain pColor src n params row free U d : ℕ} (hmain : P[pMain]? = some (body pColor))
    (R : LightColorBands.Procs P pColor) (μ : ℕ → ℤ) (p : Coloring.Parameter (width n)) (x : Fin n → ℤ) (hn : 0 < n)
    (hsrc : src + n ≤ free) (hparams : params + 19 ≤ free) (hrow : row + 6 ≤ free) (hw : (lim.space : ℤ) ≤ lim.word)
    (hspace : space free n ≤ lim.space) (hword : (word n U : ℤ) ≤ lim.word) (hd : d + depth n ≤ lim.depth)
    (hbits : μ params = (Scales.inputBits n : ℤ)) (hfields : Seg μ row (ColorParameters.fields p))
    (hinput : Seg μ src (List.ofFn x)) (hbound : ∀ i, |x i| ≤ (U : ℤ)) :
    Meets lim P pMain d [src, n, params, row, free] μ (time n) (fun r ν => Output μ ν free p x r) :=
  by
  have hW : (width n : ℤ) ≤ lim.word := (Int.ofNat_le.mpr (by unfold word; omega)).trans hword
  have hbandWord : (LightColorBands.word (width n) n n U : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (by unfold word; omega)).trans hword
  have hWork : work free n ≤ lim.space := by unfold space LightColorBands.space ColorBandBounds.space at hspace; omega
  have hfree : free ≤ work free n := by unfold work ce cv be bv ae av class2 class1 class0; omega
  have hsp : free ≤ lim.space := hfree.trans hWork
  have hptr (a : ℕ) (ha : a ≤ work free n) : (a : ℤ) ≤ lim.word := (Int.ofNat_le.mpr (ha.trans hWork)).trans hw
  have hfW := hptr free hfree
  have hc0 := hptr (class0 free n) (by unfold work ce cv be bv ae av class2 class1 class0; omega)
  have hc1 := hptr (class1 free n) (by unfold work ce cv be bv ae av class2 class1; omega)
  have hc2 := hptr (class2 free n) (by unfold work ce cv be bv ae av class2; omega)
  have hav := hptr (av free n) (by unfold work ce cv be bv ae; omega)
  have hae := hptr (ae free n) (by unfold work ce cv be bv; omega)
  have hbv := hptr (bv free n) (by unfold work ce cv be; omega)
  have hbe := hptr (be free n) (by unfold work ce cv; omega)
  have hcv := hptr (cv free n) (by unfold work ce; omega)
  have hce := hptr (ce free n) (by unfold work; omega)
  have hwk := hptr (work free n) le_rfl
  have hc0Add := hc0
  dsimp only [class0] at hc0Add
  push_cast at hc0Add
  have hc1Add := hc1
  dsimp only [class1] at hc1Add
  push_cast at hc1Add
  have hc2Add := hc2
  dsimp only [class2] at hc2Add
  push_cast at hc2Add
  have havAdd := hav
  dsimp only [av] at havAdd
  push_cast at havAdd
  have haeAdd := hae
  dsimp only [ae] at haeAdd
  push_cast at haeAdd
  have hbvAdd := hbv
  dsimp only [bv] at hbvAdd
  push_cast at hbvAdd
  have hbeAdd := hbe
  dsimp only [be] at hbeAdd
  push_cast at hbeAdd
  have hcvAdd := hcv
  dsimp only [cv] at hcvAdd
  push_cast at hcvAdd
  have hceAdd := hce
  dsimp only [ce] at hceAdd
  push_cast at hceAdd
  have hwkAdd := hwk
  dsimp only [work] at hwkAdd
  push_cast at hwkAdd
  have hnword : (n : ℤ) ≤ lim.word :=
    by
    have hh : n ≤ work free n := by unfold work ce cv be bv ae av class2 class1 class0; omega
    exact hptr n hh
  have hrowEnd : row + 6 ≤ lim.space := hrow.trans hsp
  have hparamsSpace : params < lim.space := by omega
  have hf0 := hfields 0 (by simp [ColorParameters.fields])
  have hf1 := hfields 1 (by simp [ColorParameters.fields])
  have hf2 := hfields 2 (by simp [ColorParameters.fields])
  have hf3 := hfields 3 (by simp [ColorParameters.fields])
  have hf4 := hfields 4 (by simp [ColorParameters.fields])
  have hf5 := hfields 5 (by simp [ColorParameters.fields])
  simp only [ColorParameters.fields, List.getElem_cons_zero, List.getElem_cons_succ,
    add_zero] at hf0 hf1 hf2 hf3 hf4 hf5
  have hrow1 : ((row : ℤ) + 1).toNat = row + 1 := by omega
  have hrow2 : ((row : ℤ) + 2).toNat = row + 2 := by omega
  have hrow3 : ((row : ℤ) + 3).toNat = row + 3 := by omega
  have hrow4 : ((row : ℤ) + 4).toNat = row + 4 := by omega
  have hrow5 : ((row : ℤ) + 5).toNat = row + 5 := by omega
  have hCall :=
    R.meets (d := d + 1) (src := src) (colors := free) (dst0 := class0 free n) (dst1 := class1 free n) (dst2 :=
      class2 free n) (g := n) (av := av free n) (ae := ae free n) (bv := bv free n) (be := be free n) (cv := cv free n)
      (ce := ce free n) (work := work free n) p x hw (width_sufficient n) hn hsrc le_rfl le_rfl le_rfl le_rfl le_rfl
      le_rfl le_rfl le_rfl le_rfl le_rfl hspace hbandWord (by unfold depth at hd; omega) hinput hbound
  have hD : d + 1 ≤ lim.depth := by unfold depth LightColorBands.depth at hd; omega
  have hbitsCast : (Scales.inputBits n : ℤ) + 1 = (width n : ℤ) := by simp [width]
  apply Meets.of_body hmain
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
    refine _root_.Light.Ends.setToThen (width n : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hbits, hbitsCast, LightColorBands.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hbits, hbitsCast, LightColorBands.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hbits, hbitsCast, LightColorBands.time] <;> omega)
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
    refine _root_.Light.Ends.setToThen (class0 free n : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, class0, LightColorBands.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [class0, LightColorBands.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, class0, LightColorBands.time] <;> omega)
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
    refine _root_.Light.Ends.setToThen (class1 free n : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, class1, LightColorBands.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [class1, LightColorBands.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, class1, LightColorBands.time] <;> omega)
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
    refine _root_.Light.Ends.setToThen (class2 free n : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, class2, LightColorBands.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [class2, LightColorBands.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, class2, LightColorBands.time] <;> omega)
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
    refine _root_.Light.Ends.setToThen (av free n : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, av, LightColorBands.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [av, LightColorBands.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, av, LightColorBands.time] <;> omega)
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
    refine _root_.Light.Ends.setToThen (ae free n : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ae, LightColorBands.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [ae, LightColorBands.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ae, LightColorBands.time] <;> omega)
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
    refine _root_.Light.Ends.setToThen (bv free n : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, bv, LightColorBands.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [bv, LightColorBands.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, bv, LightColorBands.time] <;> omega)
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
    refine _root_.Light.Ends.setToThen (be free n : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, be, LightColorBands.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [be, LightColorBands.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, be, LightColorBands.time] <;> omega)
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
    refine _root_.Light.Ends.setToThen (cv free n : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, cv, LightColorBands.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [cv, LightColorBands.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, cv, LightColorBands.time] <;> omega)
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
    refine _root_.Light.Ends.setToThen (ce free n : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ce, LightColorBands.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [ce, LightColorBands.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ce, LightColorBands.time] <;> omega)
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
    refine _root_.Light.Ends.setToThen (work free n : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, work, LightColorBands.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [work, LightColorBands.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, work, LightColorBands.time] <;> omega)
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
    first
    | refine _root_.Light.Ends.callToThen (hCall _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hCall ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hf0, hf1, hf2, hf3, hf4, hf5, hrow1, hrow2,
            hrow3, hrow4, hrow5, LightColorBands.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hf0, hf1, hf2, hf3, hf4, hf5, hrow1, hrow2, hrow3, hrow4, hrow5, LightColorBands.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hf0, hf1, hf2, hf3, hf4, hf5, hrow1, hrow2,
            hrow3, hrow4, hrow5, LightColorBands.time] <;> omega)
    on_goal -1 => (rintro result ν ⟨hout, hkeep⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  obtain ⟨A, hsA, B, hsB, C, hsC, hr, hA, hB, hC, htables⟩ := hout
  have hAL : A.length ≤ n := hA.2.1.trans (length_classList_le p x 0 1)
  have hBL : B.length ≤ n := hB.2.1.trans (length_classList_le p x 1 1)
  have hCL : C.length ≤ n := hC.2.1.trans (length_classList_le p x 2 (-1))
  have hAH := hA.2.2.2.1
  have hBH := hB.2.2.2.1
  have hCH := hC.2.2.2.1
  have hAWord : (A.length : ℤ) ≤ lim.word := (Int.ofNat_le.mpr hAL).trans hnword
  have hBWord : (B.length : ℤ) ≤ lim.word := (Int.ofNat_le.mpr hBL).trans hnword
  have hCWord : (C.length : ℤ) ≤ lim.word := (Int.ofNat_le.mpr hCL).trans hnword
  have hheaderAv : free + 7 ≤ av free n := by unfold av class2 class1 class0; omega
  have hheaderSpace : free + 7 ≤ lim.space :=
    by
    unfold work ce cv be bv ae av class2 class1 class0 at hWork
    omega
  have hAeSpace : free + 7 ≤ ae free n := by unfold ae; omega
  have hBeSpace : free + 7 ≤ be free n := by unfold be bv ae; omega
  have hCeSpace : free + 7 ≤ ce free n := by unfold ce cv be bv ae; omega
  have hAeReadSpace : ae free n < lim.space := by have hh := hWork; unfold work ce cv be bv at hh; omega
  have hBeReadSpace : be free n < lim.space := by have hh := hWork; unfold work ce cv at hh; omega
  have hCeReadSpace : ce free n < lim.space := by have hh := hWork; unfold work at hh; omega
  have hAeNe (k : ℕ) (hk : k < 7) : ae free n ≠ free + k := by omega
  have hBeNe (k : ℕ) (hk : k < 7) : be free n ≠ free + k := by omega
  have hCeNe (k : ℕ) (hk : k < 7) : ce free n ≠ free + k := by omega
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    refine _root_.Light.Ends.setToThen (A.length : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hAH, LightColorBands.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hAH, LightColorBands.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hAH, LightColorBands.time] <;> omega)
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
    refine _root_.Light.Ends.setToThen (B.length : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hBH, LightColorBands.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hBH, LightColorBands.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hBH, LightColorBands.time] <;> omega)
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
    refine _root_.Light.Ends.setToThen (C.length : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hCH, LightColorBands.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hCH, LightColorBands.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hCH, LightColorBands.time] <;> omega)
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
    refine _root_.Light.Ends.storeToThen free (av free n) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightColorBands.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightColorBands.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightColorBands.time] <;> omega)
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
    refine _root_.Light.Ends.storeToThen (free + 1) A.length ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightColorBands.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightColorBands.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightColorBands.time] <;> omega)
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
    refine _root_.Light.Ends.storeToThen (free + 2) (bv free n) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightColorBands.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightColorBands.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightColorBands.time] <;> omega)
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
    refine _root_.Light.Ends.storeToThen (free + 3) B.length ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightColorBands.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightColorBands.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightColorBands.time] <;> omega)
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
    refine _root_.Light.Ends.storeToThen (free + 4) (cv free n) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightColorBands.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightColorBands.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightColorBands.time] <;> omega)
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
    refine _root_.Light.Ends.storeToThen (free + 5) C.length ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightColorBands.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightColorBands.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightColorBands.time] <;> omega)
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
    refine _root_.Light.Ends.storeToThen (free + 6) (work free n) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightColorBands.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightColorBands.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightColorBands.time] <;> omega)
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
    refine _root_.Light.Ends.setToThen (free : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightColorBands.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightColorBands.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightColorBands.time] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  refine ⟨rfl, ?_, A, B, C, ?_, ?_, ?_, ?_⟩
  · ( try refine _root_.Light.SameOn.cell ?_
      intro x_p2m_4512109409172918825 hx_p2m_4512109409172918825
      first
      | ((  (repeat
                ((with_reducible rename _root_.Light.SameOn _ _ _ => h_p2m_5674586769846650197);
                  (try have := h_p2m_5674586769846650197 x_p2m_4512109409172918825 (by omega));
                  revert h_p2m_5674586769846650197))
            intros
            try simp only [_root_.Function.update_apply, _root_.Light.wrote] at *); omega)
      |
        (simp [] at hx_p2m_4512109409172918825;
          ( (repeat
                ((with_reducible rename _root_.Light.SameOn _ _ _ => h_p2m_12378595691860146426);
                  (try have := h_p2m_12378595691860146426 x_p2m_4512109409172918825 (by omega));
                  revert h_p2m_12378595691860146426))
            intros
            try simp only [_root_.Function.update_apply, _root_.Light.wrote] at *); omega)
      | ( ( (repeat
                ((with_reducible rename _root_.Light.SameOn _ _ _ => h_p2m_3205375742311293316);
                  (try have := h_p2m_3205375742311293316 x_p2m_4512109409172918825 (by omega));
                  revert h_p2m_3205375742311293316))
            intros
            try simp only [_root_.Function.update_apply, _root_.Light.wrote] at *)
          fail "The cell x may have changed. Each equation ν' x = ν x above comes from a promise \
                      SameOn K ν ν' whose condition holds at x. Look for the promise without an equation: \
                      its condition K x does not follow from the hypotheses."))
  · simp [header, seg_cons, Nat.add_assoc]
  all_goals
    refine ⟨?_, by assumption, by assumption, ?_⟩
    · intro i hi
      first
      |
        simpa only [Function.update_of_ne (by omega : av free n + i ≠ free + 6),
          Function.update_of_ne (by omega : av free n + i ≠ free + 5),
          Function.update_of_ne (by omega : av free n + i ≠ free + 4),
          Function.update_of_ne (by omega : av free n + i ≠ free + 3),
          Function.update_of_ne (by omega : av free n + i ≠ free + 2),
          Function.update_of_ne (by omega : av free n + i ≠ free + 1),
          Function.update_of_ne (by omega : av free n + i ≠ free)] using hA.1 i hi
      | have hsep : free + 7 ≤ bv free n := by unfold bv ae; omega
        simpa only [Function.update_of_ne (by omega : bv free n + i ≠ free + 6),
          Function.update_of_ne (by omega : bv free n + i ≠ free + 5),
          Function.update_of_ne (by omega : bv free n + i ≠ free + 4),
          Function.update_of_ne (by omega : bv free n + i ≠ free + 3),
          Function.update_of_ne (by omega : bv free n + i ≠ free + 2),
          Function.update_of_ne (by omega : bv free n + i ≠ free + 1),
          Function.update_of_ne (by omega : bv free n + i ≠ free)] using hB.1 i hi
      | have hsep : free + 7 ≤ cv free n := by unfold cv be bv ae; omega
        simpa only [Function.update_of_ne (by omega : cv free n + i ≠ free + 6),
          Function.update_of_ne (by omega : cv free n + i ≠ free + 5),
          Function.update_of_ne (by omega : cv free n + i ≠ free + 4),
          Function.update_of_ne (by omega : cv free n + i ≠ free + 3),
          Function.update_of_ne (by omega : cv free n + i ≠ free + 2),
          Function.update_of_ne (by omega : cv free n + i ≠ free + 1),
          Function.update_of_ne (by omega : cv free n + i ≠ free)] using hC.1 i hi
    ·
      first
      | exact hA.2.2.1
      | exact hB.2.2.1
      | exact hC.2.2.1
end ThreeSum.LightTernaryColorPrelude

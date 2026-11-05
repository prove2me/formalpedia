-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalCountFrontendBudget.physical_prefix_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T11:58:25.010006+00:00
-- url     : https://prove2.me/submissions/95c0d5a8-69bb-4629-8a80-3fce31481335

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_PreparedBudget
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_CountFrontend
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryOversizeDimensions
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_CountFrontendBudget
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalCountFrontendBudget_actual_query_envelope_volume
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalCountFrontendBudget_frontend_shape_bound
import Theorems.Thm_Light_MatAt_congr
import Theorems.Thm_Light_Seg_congr
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_P2M_ThreeSum_TernaryCoverRegularity_mapEdge_symm__4d2d267acd4d
import Theorems.Thm_P2M_ThreeSum_TernaryCoverRegularity_reindex_symm__dc387cbb7851
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_output_length
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_output_zero
import Theorems.Thm_ThreeSum_LightTernaryEnumeration_output_length
import Theorems.Thm_ThreeSum_LightTernaryEnumeration_output_zero
import Theorems.Thm_ThreeSum_LightTernaryWeightedSum_sum_zero
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_zero
import Theorems.Thm_ThreeSum_SubsetAddress_natPositions_card
import Theorems.Thm_ThreeSum_SubsetAddress_weight_zero
import Theorems.Thm_ThreeSum_TernaryAddresses_codes_length
import Theorems.Thm_ThreeSum_TernaryBankEnumeration_wordList_length
import Theorems.Thm_ThreeSum_TernaryBankEnumeration_wordList_sum
import Theorems.Thm_ThreeSum_TernaryBank_mem_bank
import Theorems.Thm_ThreeSum_TernaryBank_mem_lowerWords
import Theorems.Thm_ThreeSum_TernaryBank_mem_nearWords
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_left_mapEdge
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_left_swapEdge
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_mapEdge_symm
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_output_mapEdge
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_reindex_symm
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_right_mapEdge
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_right_swapEdge
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_swapEdge_swapEdge
import Theorems.Thm_ThreeSum_TernaryEnumeration_mem_digits
import Theorems.Thm_ThreeSum_TernaryFrozenQueryStages_coords_zero
import Theorems.Thm_ThreeSum_TernaryFrozenQueryStages_stageValue_zero
import Theorems.Thm_ThreeSum_TernaryNearEnumeration_codes_length
import Theorems.Thm_ThreeSum_TernaryNearEnumeration_mem_digits
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightCacheEnumeration_output_length
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightCacheEnumeration_output_zero
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedBankAssembly_program_length
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedBankStages_program_length
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedCountFrontend_main
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedCountFrontend_prepared
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedCountFrontend_program_length
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedCountFrontend_row
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedCountFrontend_rows
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedFrozenQuery_queryTime_zero
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedGroupedBanks_program_length
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedNearEnumeration_branchOutput_length
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedNearEnumeration_output_length
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedNearPair_program_length
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedNearSetup_program_length
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedPreparedWanted_program_length
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedWantedQuery_program_length
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedWantedRows_program_length
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedAddresses_codes_length
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedBankEnumeration_mem_bank
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedBankEnumeration_wordList_cost
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedBankEnumeration_wordList_length
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedBankStageModel_forwardStage_zero
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedEnumeration_digitCost_one
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedEnumeration_digitCost_two
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedEnumeration_digitCost_zero
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedEnumeration_mem_digits
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalBank_mem_bank
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalBank_mem_nearWords
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalOversizeDimensions_actual_bank_volume
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalOversizeDimensions_partition_le_native
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalOversizeOverhead_baseFactor_pos
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalOversizeOverhead_base_factor_prefix_bound
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalOversizeOverhead_repeated_native_family_factor_bound
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalOversizePrime_inflation_pos
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalParameters_gibbs_parameters
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedNearBankEnumeration_mem_nearWords
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedNearEnumeration_codes_length
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedNearEnumeration_mem_digits
attribute [local simp] Light.getElem_powList
attribute [local simp] Light.length_powList
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] P2M_ThreeSum_TernaryCoverRegularity_mapEdge_symm__4d2d267acd4d
attribute [local simp] P2M_ThreeSum_TernaryCoverRegularity_reindex_symm__dc387cbb7851
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices
attribute [local simp] ThreeSum.LightSubsetEnumeration.output_length
attribute [local simp] ThreeSum.LightSubsetEnumeration.output_zero
attribute [local simp] ThreeSum.LightTernaryEnumeration.output_length
attribute [local simp] ThreeSum.LightTernaryEnumeration.output_zero
attribute [local simp] ThreeSum.LightTernaryWeightedSum.sum_zero
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero
attribute [local simp] ThreeSum.TernaryAddresses.codes_length
attribute [local simp] ThreeSum.TernaryBank.mem_bank
attribute [local simp] ThreeSum.TernaryBank.mem_lowerWords
attribute [local simp] ThreeSum.TernaryBank.mem_nearWords
attribute [local simp] ThreeSum.TernaryBankEnumeration.wordList_length
attribute [local simp] ThreeSum.TernaryBankEnumeration.wordList_sum
attribute [local simp] ThreeSum.TernaryCoverRegularity.left_mapEdge
attribute [local simp] ThreeSum.TernaryCoverRegularity.left_swapEdge
attribute [local simp] ThreeSum.TernaryCoverRegularity.mapEdge_symm
attribute [local simp] ThreeSum.TernaryCoverRegularity.output_mapEdge
attribute [local simp] ThreeSum.TernaryCoverRegularity.reindex_symm
attribute [local simp] ThreeSum.TernaryCoverRegularity.right_mapEdge
attribute [local simp] ThreeSum.TernaryCoverRegularity.right_swapEdge
attribute [local simp] ThreeSum.TernaryCoverRegularity.swapEdge_swapEdge
attribute [local simp] ThreeSum.TernaryEnumeration.mem_digits
attribute [local simp] ThreeSum.TernaryFrozenQueryStages.coords_zero
attribute [local simp] ThreeSum.TernaryFrozenQueryStages.stageValue_zero
attribute [local simp] ThreeSum.TernaryNearEnumeration.codes_length
attribute [local simp] ThreeSum.TernaryNearEnumeration.mem_digits
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightCacheEnumeration.output_length
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightCacheEnumeration.output_zero
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedBankAssembly.program_length
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedBankStages.program_length
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedCountFrontend.main
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedCountFrontend.prepared
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedCountFrontend.program_length
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedCountFrontend.row
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedCountFrontend.rows
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedFrozenQuery.queryTime_zero
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGroupedBanks.program_length
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedNearEnumeration.branchOutput_length
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedNearEnumeration.output_length
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedNearPair.program_length
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedNearSetup.program_length
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedPreparedWanted.program_length
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedWantedQuery.program_length
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedWantedRows.program_length
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedAddresses.codes_length
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedBankEnumeration.mem_bank
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedBankEnumeration.wordList_cost
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedBankEnumeration.wordList_length
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedBankStageModel.forwardStage_zero
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedEnumeration.digitCost_one
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedEnumeration.digitCost_two
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedEnumeration.digitCost_zero
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedEnumeration.mem_digits
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalBank.mem_bank
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalBank.mem_nearWords
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedNearBankEnumeration.mem_nearWords
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedNearEnumeration.codes_length
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedNearEnumeration.mem_digits


namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
namespace ThreeSum.WeightedGlobalCountFrontendBudget
open Filter Real Asymptotics
open TernaryJointType WeightedGlobalBank WeightedGlobalParameters WeightedGlobalDimensionBounds
open WeightedGlobalEntropyRates WeightedGlobalLocalParameters WeightedGlobalCoverScale WeightedGlobalOversizePrime WeightedGlobalOversizeRates
open WeightedGlobalCoverCapParameters
open WeightedGlobalOversizeOverhead WeightedGlobalOversizeDimensions WeightedGlobalPrincipalDimensions
open LightWeightedNearPair
open scoped Topology
set_option maxHeartbeats 5000000
set_option maxRecDepth 16000
private theorem one_le_mul_real {a b : ℝ} (ha : 1≤a) (hb : 1≤b) : 1≤a*b := by
  nlinarith [mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hb)]
end ThreeSum.WeightedGlobalCountFrontendBudget
end
end WeightedCache3SUMRefinement_e1ae71d
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalCountFrontendBudget
open Filter Real Asymptotics
open TernaryJointType WeightedGlobalBank WeightedGlobalParameters WeightedGlobalDimensionBounds
open WeightedGlobalEntropyRates WeightedGlobalLocalParameters WeightedGlobalCoverScale WeightedGlobalOversizePrime WeightedGlobalOversizeRates
open WeightedGlobalCoverCapParameters
open WeightedGlobalOversizeOverhead WeightedGlobalOversizeDimensions WeightedGlobalPrincipalDimensions
open LightWeightedNearPair
open scoped Topology
set_option maxHeartbeats 5000000
set_option maxRecDepth 16000
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalCountFrontendBudget
theorem _root_.solution {K k m n j groups count b : ℕ}
    (hK : 0<K) (hk : 0<k) (hm : 0<m) (hn : 1<n) (hj : j≤radixLength m n)
    (c d : ℕ) (hb : b≤c*(fixedLength m+1)^d)
    (f g : Config) (hT : f.T=bankCut m j)
    (hgroups : groups≤(b*(nativeFamily K m k).length*
      WeightedGlobalCoverCapParameters.rawThreshold (nativePrime K m) (sourceCap m (nativePrime K m)) k)^j)
    (hcount : (count : ℝ)≤(n : ℝ)*((nativePrime K m : ℝ)/partitionCap m)^j*
      ((b*(nativeFamily K m k).length*
        WeightedGlobalCoverCapParameters.rawThreshold (nativePrime K m) (sourceCap m (nativePrime K m)) k : ℕ) : ℝ)^j) :
    (LightWeightedCountFrontend.time groups (fixedLength (j*m)) f.L (bankSize m j) count (queryMax m j f g)+1000 : ℕ)≤
      dimensionConstant K k c d m*(width (fixedLength (j*m)) f g : ℝ)^3*
        (n : ℝ)^principalExponent K k c d m := by
  let S := (inflation K m : ℝ)^(4*j)
  let B := (baseFactor K k c d m : ℝ)^j
  let X := (n : ℝ)*((nativePrime K m : ℝ)/partitionCap m)^j
  have hs : (1 : ℝ)≤ inflation K m := by exact_mod_cast inflation_pos hK m
  have hbpos : (1 : ℝ)≤baseFactor K k c d m := by exact_mod_cast baseFactor_pos K k c d m
  have hS : 1≤S := one_le_pow₀ hs
  have hB : 1≤B := one_le_pow₀ hbpos
  have hR : 0<(partitionCap m : ℝ) := by unfold partitionCap; positivity
  have hpR : (partitionCap m : ℝ)≤nativePrime K m := by exact_mod_cast partition_le_native hK m
  have hratio : 1≤(nativePrime K m : ℝ)/partitionCap m := (one_le_div hR).mpr hpR
  have hX : 1≤X := one_le_mul_real (by exact_mod_cast hn.le) (one_le_pow₀ hratio)
  have hfacN := repeated_native_family_factor_bound K k c d m b j hb
  have hfac : (((b*(nativeFamily K m k).length*
      WeightedGlobalCoverCapParameters.rawThreshold (nativePrime K m) (sourceCap m (nativePrime K m)) k : ℕ) : ℝ)^j)≤S*B := by
    dsimp [S,B]
    exact_mod_cast hfacN
  have hgR : (groups : ℝ)≤S*B := (by exact_mod_cast hgroups : (groups : ℝ)≤_).trans hfac
  have hcR : (count : ℝ)≤X*(S*B) := hcount.trans (mul_le_mul_of_nonneg_left hfac (show 0≤X from by linarith))
  have ht := frontend_shape_bound f g hT (S*B) X (one_le_mul_real hS hB) hX hgR hcR
  have hbVol := WeightedGlobalOversizeDimensions.actual_bank_volume hK hm hn hj
  have hqVol := actual_query_envelope_volume hK hm hn hj
  have hvol : S*((bankSize m j : ℝ)+X*envelope m j)≤
      (Real.exp (WeightedGlobalOversizeDimensions.bankSlope K m)+Real.exp (WeightedGlobalOversizeDimensions.querySlope K m)/z^2739)*
        (n : ℝ)^max (WeightedGlobalOversizeRates.bankCharge K m) (WeightedGlobalOversizeRates.queryCharge K m) := by
    have hnr : (1 : ℝ)≤n := by exact_mod_cast hn.le
    have h1 := Real.rpow_le_rpow_of_exponent_le hnr (le_max_left (WeightedGlobalOversizeRates.bankCharge K m) (WeightedGlobalOversizeRates.queryCharge K m))
    have h2 := Real.rpow_le_rpow_of_exponent_le hnr (le_max_right (WeightedGlobalOversizeRates.bankCharge K m) (WeightedGlobalOversizeRates.queryCharge K m))
    have hB' := hbVol.trans (mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le)
    have hQ' := hqVol.trans (mul_le_mul_of_nonneg_left h2 (div_pos (Real.exp_pos _) (pow_pos gibbs_parameters.2.2.1 2739)).le)
    dsimp [S,X] at *
    nlinarith only [hB',hQ']
  have hbase := base_factor_prefix_bound hK hk hm hn hj c d
  change B≤(baseFactor K k c d m : ℝ)*(n : ℝ)^overheadCharge k c d m at hbase
  have hmain := mul_le_mul_of_nonneg_left hvol (by positivity : 0≤1000000*(width (fixedLength (j*m)) f g : ℝ)^3*B)
  have hbase' := mul_le_mul_of_nonneg_right hbase
    (by have hz := gibbs_parameters.2.2.1; positivity : 0≤1000000*(width (fixedLength (j*m)) f g : ℝ)^3*
      (Real.exp (WeightedGlobalOversizeDimensions.bankSlope K m)+Real.exp (WeightedGlobalOversizeDimensions.querySlope K m)/z^2739)*
      (n : ℝ)^max (WeightedGlobalOversizeRates.bankCharge K m) (WeightedGlobalOversizeRates.queryCharge K m))
  have hnR : 0<(n : ℝ) := by exact_mod_cast lt_trans Nat.zero_lt_one hn
  have heq : (n : ℝ)^overheadCharge k c d m*(n : ℝ)^max (WeightedGlobalOversizeRates.bankCharge K m) (WeightedGlobalOversizeRates.queryCharge K m)=
      (n : ℝ)^principalExponent K k c d m := by rw [←Real.rpow_add hnR]; congr 1; unfold principalExponent; ring
  calc
    _≤1000000*(width (fixedLength (j*m)) f g : ℝ)^3*(S*B)*
      ((bankSize m j : ℝ)+X*envelope m j) := ht
    _=1000000*(width (fixedLength (j*m)) f g : ℝ)^3*B*
      (S*((bankSize m j : ℝ)+X*envelope m j)) := by ring
    _≤1000000*(width (fixedLength (j*m)) f g : ℝ)^3*B*
      ((Real.exp (WeightedGlobalOversizeDimensions.bankSlope K m)+Real.exp (WeightedGlobalOversizeDimensions.querySlope K m)/z^2739)*
        (n : ℝ)^max (WeightedGlobalOversizeRates.bankCharge K m) (WeightedGlobalOversizeRates.queryCharge K m)) := hmain
    _=B*(1000000*(width (fixedLength (j*m)) f g : ℝ)^3*
      (Real.exp (WeightedGlobalOversizeDimensions.bankSlope K m)+Real.exp (WeightedGlobalOversizeDimensions.querySlope K m)/z^2739)*
        (n : ℝ)^max (WeightedGlobalOversizeRates.bankCharge K m) (WeightedGlobalOversizeRates.queryCharge K m)) := by ring
    _≤_ := hbase'
    _=dimensionConstant K k c d m*(width (fixedLength (j*m)) f g : ℝ)^3*
      (n : ℝ)^principalExponent K k c d m := by
      unfold dimensionConstant
      rw [show (baseFactor K k c d m : ℝ)*(n : ℝ)^overheadCharge k c d m*
        (1000000*(width (fixedLength (j*m)) f g : ℝ)^3*
          (Real.exp (WeightedGlobalOversizeDimensions.bankSlope K m)+Real.exp (WeightedGlobalOversizeDimensions.querySlope K m)/z^2739)*
          (n : ℝ)^max (WeightedGlobalOversizeRates.bankCharge K m) (WeightedGlobalOversizeRates.queryCharge K m))=
        (1000000*(baseFactor K k c d m : ℝ)*
          (Real.exp (WeightedGlobalOversizeDimensions.bankSlope K m)+Real.exp (WeightedGlobalOversizeDimensions.querySlope K m)/z^2739)*
          (width (fixedLength (j*m)) f g : ℝ)^3)*
          ((n : ℝ)^overheadCharge k c d m*(n : ℝ)^max (WeightedGlobalOversizeRates.bankCharge K m) (WeightedGlobalOversizeRates.queryCharge K m)) by ring,
        heq]
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalCountFrontendBudget

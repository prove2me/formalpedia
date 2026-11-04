-- Prove2me | solution 1 for ThreeSum.WeightedGlobalCountFrontendBudget.all_prefix_time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T14:32:48.606736+00:00
-- url     : https://prove2.me/submissions/8bebf5e5-191c-4d41-8aab-b36124d4b84f

import Definitions.Def_Submission_Weighted_PreparedBudget
import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_CountFrontend
import Definitions.Def_Submission_Weighted_Global_TernaryOversizeDimensions
import Definitions.Def_Submission_Weighted_Global_CountFrontendBudget
import Theorems.Thm_ThreeSum_WeightedGlobalCountFrontendBudget_dimensionConstant_nonneg
import Theorems.Thm_ThreeSum_WeightedGlobalCountFrontendBudget_physical_prefix_bound
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
import Theorems.Thm_ThreeSum_LightCacheEnumeration_output_length
import Theorems.Thm_ThreeSum_LightCacheEnumeration_output_zero
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_output_length
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_output_zero
import Theorems.Thm_ThreeSum_LightTernaryEnumeration_output_length
import Theorems.Thm_ThreeSum_LightTernaryEnumeration_output_zero
import Theorems.Thm_ThreeSum_LightTernaryWeightedSum_sum_zero
import Theorems.Thm_ThreeSum_LightWeightedBankAssembly_program_length
import Theorems.Thm_ThreeSum_LightWeightedBankStages_program_length
import Theorems.Thm_ThreeSum_LightWeightedCountFrontend_main
import Theorems.Thm_ThreeSum_LightWeightedCountFrontend_prepared
import Theorems.Thm_ThreeSum_LightWeightedCountFrontend_program_length
import Theorems.Thm_ThreeSum_LightWeightedCountFrontend_row
import Theorems.Thm_ThreeSum_LightWeightedCountFrontend_rows
import Theorems.Thm_ThreeSum_LightWeightedFrozenQuery_queryTime_zero
import Theorems.Thm_ThreeSum_LightWeightedGroupedBanks_program_length
import Theorems.Thm_ThreeSum_LightWeightedNearEnumeration_branchOutput_length
import Theorems.Thm_ThreeSum_LightWeightedNearEnumeration_output_length
import Theorems.Thm_ThreeSum_LightWeightedNearPair_program_length
import Theorems.Thm_ThreeSum_LightWeightedNearSetup_program_length
import Theorems.Thm_ThreeSum_LightWeightedPreparedWanted_program_length
import Theorems.Thm_ThreeSum_LightWeightedWantedQuery_program_length
import Theorems.Thm_ThreeSum_LightWeightedWantedRows_program_length
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
import Theorems.Thm_ThreeSum_WeightedAddresses_codes_length
import Theorems.Thm_ThreeSum_WeightedBankEnumeration_mem_bank
import Theorems.Thm_ThreeSum_WeightedBankEnumeration_wordList_cost
import Theorems.Thm_ThreeSum_WeightedBankEnumeration_wordList_length
import Theorems.Thm_ThreeSum_WeightedBankStageModel_forwardStage_zero
import Theorems.Thm_ThreeSum_WeightedEnumeration_digitCost_one
import Theorems.Thm_ThreeSum_WeightedEnumeration_digitCost_two
import Theorems.Thm_ThreeSum_WeightedEnumeration_digitCost_zero
import Theorems.Thm_ThreeSum_WeightedEnumeration_mem_digits
import Theorems.Thm_ThreeSum_WeightedGlobalBank_mem_bank
import Theorems.Thm_ThreeSum_WeightedGlobalBank_mem_nearWords
import Theorems.Thm_ThreeSum_WeightedNearBankEnumeration_mem_nearWords
import Theorems.Thm_ThreeSum_WeightedNearEnumeration_codes_length
import Theorems.Thm_ThreeSum_WeightedNearEnumeration_mem_digits
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
attribute [local simp] ThreeSum.LightCacheEnumeration.output_length
attribute [local simp] ThreeSum.LightCacheEnumeration.output_zero
attribute [local simp] ThreeSum.LightSubsetEnumeration.output_length
attribute [local simp] ThreeSum.LightSubsetEnumeration.output_zero
attribute [local simp] ThreeSum.LightTernaryEnumeration.output_length
attribute [local simp] ThreeSum.LightTernaryEnumeration.output_zero
attribute [local simp] ThreeSum.LightTernaryWeightedSum.sum_zero
attribute [local simp] ThreeSum.LightWeightedBankAssembly.program_length
attribute [local simp] ThreeSum.LightWeightedBankStages.program_length
attribute [local simp] ThreeSum.LightWeightedCountFrontend.main
attribute [local simp] ThreeSum.LightWeightedCountFrontend.prepared
attribute [local simp] ThreeSum.LightWeightedCountFrontend.program_length
attribute [local simp] ThreeSum.LightWeightedCountFrontend.row
attribute [local simp] ThreeSum.LightWeightedCountFrontend.rows
attribute [local simp] ThreeSum.LightWeightedFrozenQuery.queryTime_zero
attribute [local simp] ThreeSum.LightWeightedGroupedBanks.program_length
attribute [local simp] ThreeSum.LightWeightedNearEnumeration.branchOutput_length
attribute [local simp] ThreeSum.LightWeightedNearEnumeration.output_length
attribute [local simp] ThreeSum.LightWeightedNearPair.program_length
attribute [local simp] ThreeSum.LightWeightedNearSetup.program_length
attribute [local simp] ThreeSum.LightWeightedPreparedWanted.program_length
attribute [local simp] ThreeSum.LightWeightedWantedQuery.program_length
attribute [local simp] ThreeSum.LightWeightedWantedRows.program_length
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
attribute [local simp] ThreeSum.WeightedAddresses.codes_length
attribute [local simp] ThreeSum.WeightedBankEnumeration.mem_bank
attribute [local simp] ThreeSum.WeightedBankEnumeration.wordList_cost
attribute [local simp] ThreeSum.WeightedBankEnumeration.wordList_length
attribute [local simp] ThreeSum.WeightedBankStageModel.forwardStage_zero
attribute [local simp] ThreeSum.WeightedEnumeration.digitCost_one
attribute [local simp] ThreeSum.WeightedEnumeration.digitCost_two
attribute [local simp] ThreeSum.WeightedEnumeration.digitCost_zero
attribute [local simp] ThreeSum.WeightedEnumeration.mem_digits
attribute [local simp] ThreeSum.WeightedGlobalBank.mem_bank
attribute [local simp] ThreeSum.WeightedGlobalBank.mem_nearWords
attribute [local simp] ThreeSum.WeightedNearBankEnumeration.mem_nearWords
attribute [local simp] ThreeSum.WeightedNearEnumeration.codes_length
attribute [local simp] ThreeSum.WeightedNearEnumeration.mem_digits



set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalCountFrontendBudget
open Filter Real Asymptotics
open TernaryJointType WeightedGlobalBank WeightedGlobalParameters WeightedGlobalDimensionBounds
open WeightedGlobalEntropyRates WeightedGlobalLocalParameters WeightedGlobalCoverScale WeightedGlobalOversizePrime WeightedGlobalOversizeRates
open WeightedGlobalCoverCapParameters
open WeightedGlobalOversizeOverhead WeightedGlobalOversizeDimensions WeightedGlobalPrincipalDimensions
open LightWeightedNearPair
open scoped Topology
set_option maxHeartbeats 5000000
set_option maxRecDepth 16000
namespace ThreeSum.WeightedGlobalCountFrontendBudget
theorem _root_.solution {K k m b C A degree : ℕ}
    (hK : 0<K) (hk : 0<k) (hm : 0<m) (c d : ℕ) (hb : b≤c*(fixedLength m+1)^d)
    (f g : ℕ→ℕ→Config) (groups wanted : ℕ→ℕ→ℕ) (channels : ℕ→ℕ)
    (hT : ∀ n, 1<n → ∀ j≤radixLength m n, (f n j).T=bankCut m j)
    (hgroups : ∀ n, 1<n → ∀ j≤radixLength m n, groups n j≤
      (b*(nativeFamily K m k).length*rawThreshold (nativePrime K m) (sourceCap m (nativePrime K m)) k)^j)
    (hwanted : ∀ n, 1<n → ∀ j≤radixLength m n, (wanted n j : ℝ)≤
      (n : ℝ)*((nativePrime K m : ℝ)/partitionCap m)^j*
        ((b*(nativeFamily K m k).length*rawThreshold (nativePrime K m) (sourceCap m (nativePrime K m)) k : ℕ) : ℝ)^j)
    (hwidth : ∀ n, 1<n → ∀ j≤radixLength m n,
      width (fixedLength (j*m)) (f n j) (g n j)≤C*(radixLength m n+1))
    (hchannels : ∀ n, 1<n → channels n≤A*(radixLength m n+1)^degree)
    (n : ℕ) (hn : 1<n) :
    (allPrefixTime m f g groups wanted channels n : ℝ)≤
      ((A : ℝ)*dimensionConstant K k c d m*(C : ℝ)^3)*((radixLength m n : ℝ)+1)^(degree+4)*
        (n : ℝ)^principalExponent K k c d m := by
  let R := ((radixLength m n : ℝ)+1)
  let E := (n : ℝ)^principalExponent K k c d m
  let D := dimensionConstant K k c d m
  have hD : 0≤D := dimensionConstant_nonneg K k c d m
  have hR : 0≤R := by dsimp [R]; positivity
  have hE : 0≤E := by dsimp [E]; positivity
  have hp : ∀ j∈Finset.range (radixLength m n+1),
      (prefixTime m n j (f n j) (g n j) (groups n j) (wanted n j) : ℝ)≤D*(C : ℝ)^3*R^3*E := by
    intro j hj
    have hj' : j≤radixLength m n := by have := Finset.mem_range.mp hj; omega
    have h := physical_prefix_bound hK hk hm hn hj' c d hb (f n j) (g n j)
      (hT n hn j hj') (hgroups n hn j hj') (hwanted n hn j hj')
    have hw : (width (fixedLength (j*m)) (f n j) (g n j) : ℝ)≤(C : ℝ)*R := by
      dsimp [R]
      exact_mod_cast hwidth n hn j hj'
    have hw3 := pow_le_pow_left₀ (by positivity : (0 : ℝ)≤width (fixedLength (j*m)) (f n j) (g n j)) hw 3
    have hmul := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hw3 hD) hE
    change _≤D*(C : ℝ)^3*R^3*E
    dsimp [D,E] at hmul
    exact h.trans (by simpa only [mul_pow,mul_assoc] using hmul)
  have hsum : ((∑ j ∈ Finset.range (radixLength m n+1),
      prefixTime m n j (f n j) (g n j) (groups n j) (wanted n j) : ℕ) : ℝ)≤D*(C : ℝ)^3*R^4*E := by
    rw [Nat.cast_sum]
    have h := Finset.sum_le_sum hp
    have he : (∑ _j ∈ Finset.range (radixLength m n+1), D*(C : ℝ)^3*R^3*E)=D*(C : ℝ)^3*R^4*E := by
      simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
      dsimp [R]
      push_cast
      ring
    exact h.trans_eq he
  have hchan : (channels n : ℝ)≤(A : ℝ)*R^degree := by dsimp [R]; exact_mod_cast hchannels n hn
  have htotal := mul_le_mul hchan hsum (by positivity : (0 : ℝ)≤
    ((∑ j ∈ Finset.range (radixLength m n+1), prefixTime m n j (f n j) (g n j) (groups n j) (wanted n j) : ℕ) : ℝ))
      (by positivity : (0 : ℝ)≤(A : ℝ)*R^degree)
  unfold allPrefixTime
  rw [Nat.cast_mul]
  change _≤((A : ℝ)*D*(C : ℝ)^3)*R^(degree+4)*E
  exact htotal.trans_eq (by rw [pow_add]; ring)
end ThreeSum.WeightedGlobalCountFrontendBudget

-- Prove2me | solution 1 for ThreeSum.LightTernaryBankAssembly.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:12:31.259134+00:00
-- url     : https://prove2.me/submissions/cf9076d3-2b31-471a-aa1b-1cae17f95413

import Definitions.Def_Submission_ThreeSum_LightTernaryBankAssembly
import Definitions.Def_Submission_ThreeSum_LightTernaryBankResources
import Theorems.Thm_ThreeSum_LightTernaryBankCoordinate_time_bound
import Theorems.Thm_ThreeSum_LightTernaryBankSweep_time_bound
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_LightMaskBits_time_bound
import Theorems.Thm_ThreeSum_LightTernaryBankAssembly_program_length
import Theorems.Thm_ThreeSum_LightTernaryBankStages_program_length
import Theorems.Thm_ThreeSum_LightTernaryInversePass_time_bound
import Theorems.Thm_ThreeSum_LightTernaryLookup_time_bound
import Theorems.Thm_ThreeSum_LightTernaryMetadata_time_bound
import Theorems.Thm_ThreeSum_LightTernaryPass_time_bound
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_zero
import Theorems.Thm_ThreeSum_SubsetAddress_natPositions_card
import Theorems.Thm_ThreeSum_SubsetAddress_weight_zero
import Theorems.Thm_ThreeSum_TernaryAddresses_codes_length
import Theorems.Thm_ThreeSum_TernaryBankEnumeration_wordList_length
import Theorems.Thm_ThreeSum_TernaryBankEnumeration_wordList_sum
import Theorems.Thm_ThreeSum_TernaryBankStageModel_forwardStage_zero
import Theorems.Thm_ThreeSum_TernaryBank_mem_bank
import Theorems.Thm_ThreeSum_TernaryBank_mem_lowerWords
import Theorems.Thm_ThreeSum_TernaryBank_mem_nearWords
import Theorems.Thm_ThreeSum_TernaryEnumeration_mem_digits
import Theorems.Thm_ThreeSum_TernaryFrozenQueryStages_coords_zero
import Theorems.Thm_ThreeSum_TernaryFrozenQueryStages_stageValue_zero
attribute [local simp] Light.getElem_powList
attribute [local simp] Light.length_powList
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.LightTernaryBankAssembly.program_length
attribute [local simp] ThreeSum.LightTernaryBankStages.program_length
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
attribute [local simp] ThreeSum.TernaryBankStageModel.forwardStage_zero
attribute [local simp] ThreeSum.TernaryEnumeration.mem_digits
attribute [local simp] ThreeSum.TernaryFrozenQueryStages.coords_zero
attribute [local simp] ThreeSum.TernaryFrozenQueryStages.stageValue_zero



set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryBankAssembly
namespace ThreeSum.LightTernaryBankAssembly
theorem _root_.solution (N L n : ℕ) : time N L n≤20000*(N+1)*(N+L+1)*(n+1) := by
  have hs := LightTernaryBankSweep.time_bound N L n
  have hscale : n+1≤(N+1)*(N+L+1)*(n+1) := by
    have hpos : 1≤(N+1)*(N+L+1) := Nat.succ_le_of_lt (by positivity)
    simpa using Nat.mul_le_mul_right (n+1) hpos
  unfold time LightTernaryProduct.time
  nlinarith only [hs,hscale]
end ThreeSum.LightTernaryBankAssembly

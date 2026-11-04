-- Prove2me | solution 1 for ThreeSum.LightTernaryFrozenQuery.queryTime_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:40:01.684613+00:00
-- url     : https://prove2.me/submissions/ac8980a6-ccf5-4f09-be55-aa5cd8d4399f

import Definitions.Def_Submission_ThreeSum_LightTernaryFrozenQueryPrepare
import Definitions.Def_Submission_ThreeSum_TernaryFrozenQueryCost
import Definitions.Def_Submission_ThreeSum_LightTernaryFrozenQueryTime
import Theorems.Thm_ThreeSum_LightTernaryFrozenQuery_queryTime_zero
import Theorems.Thm_Light_LocalsBut_update
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
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
import Theorems.Thm_ThreeSum_TernaryEnumeration_mem_digits
import Theorems.Thm_ThreeSum_TernaryFrozenQueryStages_coords_succ
import Theorems.Thm_ThreeSum_TernaryFrozenQueryStages_coords_zero
import Theorems.Thm_ThreeSum_TernaryFrozenQueryStages_stageValue_zero
import Theorems.Thm_ThreeSum_TernaryNearEnumeration_codes_length
import Theorems.Thm_ThreeSum_TernaryNearEnumeration_mem_digits
attribute [local simp] Light.getElem_powList
attribute [local simp] Light.length_powList
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
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
attribute [local simp] ThreeSum.TernaryEnumeration.mem_digits
attribute [local simp] ThreeSum.TernaryFrozenQueryStages.coords_zero
attribute [local simp] ThreeSum.TernaryFrozenQueryStages.stageValue_zero
attribute [local simp] ThreeSum.TernaryNearEnumeration.codes_length
attribute [local simp] ThreeSum.TernaryNearEnumeration.mem_digits


attribute [local simp] ThreeSum.LightTernaryFrozenQuery.queryTime_zero

set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryFrozenQuery
open ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryFrozenQueryStages
open ThreeSum.TernaryFrozenQueryCost
set_option maxHeartbeats 3000000
namespace ThreeSum.LightTernaryFrozenQuery
theorem _root_.solution {N K : ℕ} (L T : ℕ) (R : TritWord N) (hK : K<N)
    (hbank : T<rank R) :
    let i : Fin N :=⟨K,hK⟩
    let t := fun d : Fin 3 => if d≤R i then queryTime L T K (Function.update R i d) else 0
    prepTime N+(t 0+t 1+t 2+200)≤queryTime L T (K+1) R := by
  dsimp only
  have hsum :
      (if (0 : Fin 3)≤R ⟨K,hK⟩ then queryTime L T K (Function.update R ⟨K,hK⟩ 0) else 0)+
      (if (1 : Fin 3)≤R ⟨K,hK⟩ then queryTime L T K (Function.update R ⟨K,hK⟩ 1) else 0)+
      (if (2 : Fin 3)≤R ⟨K,hK⟩ then queryTime L T K (Function.update R ⟨K,hK⟩ 2) else 0) =
      10000*(N+L+1)*(∑ d : Fin 3, if d≤R ⟨K,hK⟩ then
        work T (coords N K) (Function.update R ⟨K,hK⟩ d) else 0) := by
    simp [queryTime,Fin.sum_univ_succ,mul_ite,Nat.mul_add,Nat.add_assoc]
  rw [hsum,queryTime,coords_succ hK,work,if_neg (by omega : ¬rank R≤T)]
  unfold prepTime LightTernaryCodes.digitTime LightTernaryCodes.zeroTime LightMaskErase.time
  simp only [Nat.mul_add,Nat.mul_one]
  omega
end ThreeSum.LightTernaryFrozenQuery

-- Prove2me | solution 1 for ThreeSum.LightTernaryNearEnumerationMain.time_gibbs_counts
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:32:52.663642+00:00
-- url     : https://prove2.me/submissions/a862dbc5-67d3-424a-a8c0-dcd9d13ce1b6

import Definitions.Def_Submission_ThreeSum_LightTernaryNearEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryNearBankEnumeration
import Definitions.Def_Submission_ThreeSum_LightTernaryNearEnumerationMain
import Theorems.Thm_ThreeSum_LightTernaryNearEnumerationMain_time_bank_bound
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_output_length
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_output_zero
import Theorems.Thm_ThreeSum_LightTernaryEnumeration_output_length
import Theorems.Thm_ThreeSum_LightTernaryEnumeration_output_zero
import Theorems.Thm_ThreeSum_LightTernaryNearEnumeration_branchOutput_length
import Theorems.Thm_ThreeSum_LightTernaryNearEnumeration_output_length
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
import Theorems.Thm_ThreeSum_TernaryBank_nearWords_card_gibbs_counts
import Theorems.Thm_ThreeSum_TernaryEnumeration_mem_digits
import Theorems.Thm_ThreeSum_TernaryNearEnumeration_codes_length
import Theorems.Thm_ThreeSum_TernaryNearEnumeration_mem_digits
attribute [local simp] Light.getElem_powList
attribute [local simp] Light.length_powList
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.LightSubsetEnumeration.output_length
attribute [local simp] ThreeSum.LightSubsetEnumeration.output_zero
attribute [local simp] ThreeSum.LightTernaryEnumeration.output_length
attribute [local simp] ThreeSum.LightTernaryEnumeration.output_zero
attribute [local simp] ThreeSum.LightTernaryNearEnumeration.branchOutput_length
attribute [local simp] ThreeSum.LightTernaryNearEnumeration.output_length
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
attribute [local simp] ThreeSum.TernaryNearEnumeration.codes_length
attribute [local simp] ThreeSum.TernaryNearEnumeration.mem_digits



set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryNearEnumerationMain
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryAddresses
open ThreeSum.TernaryNearEnumeration ThreeSum.LightTernaryNearEnumeration
set_option maxHeartbeats 3000000
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightTernaryNearEnumerationMain
theorem _root_.solution {N : ℕ} (Q : ThreeSum.TernaryJointType.TritWord N)
    (D : ℕ) (z : ℝ) (hz : 0≤z) (hz1 : z≤1) :
    (time (ThreeSum.TernaryBankEnumeration.wordList Q) D : ℝ)*z^D ≤
      900*(N+1)*(1+z)^ThreeSum.TernaryJointType.digitCount Q 1 *
        (1+z+z^2)^ThreeSum.TernaryJointType.digitCount Q 2 := by
  have htime : (time (ThreeSum.TernaryBankEnumeration.wordList Q) D : ℝ) ≤
      900*(N+1)*(ThreeSum.TernaryBank.nearWords Q D).card := by
    exact_mod_cast (show time (ThreeSum.TernaryBankEnumeration.wordList Q) D ≤
      900*(N+1)*(ThreeSum.TernaryBank.nearWords Q D).card by
        simpa [Nat.mul_assoc] using time_bank_bound Q D)
  have hg := ThreeSum.TernaryBank.nearWords_card_gibbs_counts Q D z hz hz1
  calc
    (time (ThreeSum.TernaryBankEnumeration.wordList Q) D : ℝ)*z^D ≤
        (900*(N+1)*(ThreeSum.TernaryBank.nearWords Q D).card)*z^D :=
      mul_le_mul_of_nonneg_right htime (pow_nonneg hz D)
    _ = (900*(N+1))*((ThreeSum.TernaryBank.nearWords Q D).card*z^D) := by ring
    _ ≤ (900*(N+1))*((1+z)^ThreeSum.TernaryJointType.digitCount Q 1 *
        (1+z+z^2)^ThreeSum.TernaryJointType.digitCount Q 2) :=
      mul_le_mul_of_nonneg_left hg (by positivity)
    _ = 900*(N+1)*(1+z)^ThreeSum.TernaryJointType.digitCount Q 1 *
        (1+z+z^2)^ThreeSum.TernaryJointType.digitCount Q 2 := by ring
end ThreeSum.LightTernaryNearEnumerationMain

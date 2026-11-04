-- Prove2me | solution 1 for ThreeSum.LightTernaryNearEnumeration.map_cons_output
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:40:06.112605+00:00
-- url     : https://prove2.me/submissions/fc648407-6e78-490c-879f-378f21000ad5

import Definitions.Def_Submission_ThreeSum_LightTernaryEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryNearEnumeration
import Definitions.Def_Submission_ThreeSum_LightTernaryNearEnumeration
import Theorems.Thm_ThreeSum_LightTernaryNearEnumeration_output_length
import Theorems.Thm_ThreeSum_LightTernaryNearEnumeration_branchOutput_length
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
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_zero
import Theorems.Thm_ThreeSum_SubsetAddress_natPositions_card
import Theorems.Thm_ThreeSum_SubsetAddress_weight_zero
import Theorems.Thm_ThreeSum_TernaryAddresses_codes_length
import Theorems.Thm_ThreeSum_TernaryEnumeration_mem_digits
import Theorems.Thm_ThreeSum_TernaryEnumeration_mem_words
import Theorems.Thm_ThreeSum_TernaryNearEnumeration_admitted_length
import Theorems.Thm_ThreeSum_TernaryNearEnumeration_codes_length
import Theorems.Thm_ThreeSum_TernaryNearEnumeration_mem_digits
import Theorems.Thm_ThreeSum_TernaryNearEnumeration_mem_words
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
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero
attribute [local simp] ThreeSum.TernaryAddresses.codes_length
attribute [local simp] ThreeSum.TernaryEnumeration.mem_digits
attribute [local simp] ThreeSum.TernaryNearEnumeration.codes_length
attribute [local simp] ThreeSum.TernaryNearEnumeration.mem_digits


attribute [local simp] ThreeSum.LightTernaryNearEnumeration.output_length
attribute [local simp] ThreeSum.LightTernaryNearEnumeration.branchOutput_length

set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryNearEnumeration
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryAddresses
open ThreeSum.TernaryNearEnumeration
set_option maxHeartbeats 3000000
namespace ThreeSum.LightTernaryNearEnumeration
theorem _root_.solution (qs : List ℕ) (D pref r : ℕ) :
    (words qs D).map (fun rs => ((pref+code (r::rs) : ℕ) : ℤ)) =
      output qs D (pref+digitCode r*4^qs.length) := by
  unfold output
  apply List.map_congr_left
  intro rs hrs
  have hlen := admitted_length ((mem_words qs rs D).mp hrs)
  simp [code,hlen,Nat.add_assoc]
end ThreeSum.LightTernaryNearEnumeration

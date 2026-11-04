-- Prove2me | solution 1 for ThreeSum.LightDownsetEnumerationSetup.time_bound_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:10:28.452461+00:00
-- url     : https://prove2.me/submissions/b132ab4a-3bfe-4db5-97ba-423b788cf92c

import Definitions.Def_Submission_ThreeSum_LightDownsetEnumeration
import Definitions.Def_Submission_ThreeSum_LightDownsetEnumerationSetup
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Definitions.Def_WeightedCache3SUM_Alias_f1b1ba0c94539568
import Theorems.Thm_ThreeSum_LightSubsetEnumerationSetup_time_bound
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_output_length
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_output_zero
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_time_bound
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_zero
import Theorems.Thm_ThreeSum_SubsetAddress_natPositions_card
import Theorems.Thm_ThreeSum_SubsetAddress_weight_zero
attribute [local simp] Light.getElem_powList
attribute [local simp] Light.length_powList
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.LightSubsetEnumeration.output_length
attribute [local simp] ThreeSum.LightSubsetEnumeration.output_zero
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero



set_option autoImplicit false
open ThreeSum ThreeSum.LightDownsetEnumerationSetup
open Light ThreeSum.SubsetAddress ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightDownsetEnumerationSetup
theorem _root_.solution {L cut : ℕ} (hcut : cut ≤ L) :
    time L cut ≤ 1200*(L+1)^2*(downsetCap L cut+1) := by
  have h := LightDownsetEnumeration.time_bound hcut
  have hL : L+1 ≤ (L+1)^2*(downsetCap L cut+1) := by
    have hs : L+1 ≤ (L+1)^2 := by
      calc
        L+1 ≤ (L+1)*(L+1) := Nat.le_mul_of_pos_left _ (by omega)
        _ = (L+1)^2 := (pow_two _).symm
    exact hs.trans (Nat.le_mul_of_pos_right _ (by omega))
  have hp : 1 ≤ (L+1)^2*(downsetCap L cut+1) := by omega
  unfold time powTableTime
  have ht : LightDownsetEnumeration.time L cut ≤
      1000*((L+1)^2*(downsetCap L cut+1)) := by simpa only [Nat.mul_assoc] using h
  calc
    _ ≤ 1200*((L+1)^2*(downsetCap L cut+1)) := by omega
    _ = _ := by ring
end ThreeSum.LightDownsetEnumerationSetup

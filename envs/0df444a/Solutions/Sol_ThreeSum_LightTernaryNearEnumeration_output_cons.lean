-- Prove2me | solution 1 for ThreeSum.LightTernaryNearEnumeration.output_cons
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:45:20.864556+00:00
-- url     : https://prove2.me/submissions/a3415d55-bbb0-4cfc-8e73-66a45acdd87b

import Definitions.Def_Submission_ThreeSum_LightTernaryEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryNearEnumeration
import Definitions.Def_Submission_ThreeSum_LightTernaryNearEnumeration
import Theorems.Thm_ThreeSum_LightTernaryNearEnumeration_output_length
import Theorems.Thm_ThreeSum_LightTernaryNearEnumeration_branchOutput_length
import Theorems.Thm_ThreeSum_LightTernaryNearEnumeration_map_cons_output
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
theorem _root_.solution (q : Fin 3) (qs : List ℕ) (D pref : ℕ) :
    output (q.val :: qs) D pref = branchOutput qs D pref q.val 0 ++
      branchOutput qs D pref q.val 1 ++ branchOutput qs D pref q.val 2 := by
  have hgeneral : output (q.val::qs) D pref = (digits q.val D).flatMap
      (fun r => output qs (D-(q.val-r)) (pref+digitCode r*4^qs.length)) := by
    unfold output
    rw [words,List.map_flatMap]
    apply List.flatMap_congr
    intro r hr
    rw [List.map_map]
    exact map_cons_output qs (D-(q.val-r)) pref r
  rw [hgeneral]
  fin_cases q
  · simp [digits,List.range_succ,branchOutput,Allowed,digitCode]
  · cases D with
    | zero => simp [digits,List.range_succ,branchOutput,Allowed,digitCode]
    | succ D => simp [digits,List.range_succ,branchOutput,Allowed,digitCode,
        show 1 ≤ D+1 by omega]
  · cases D with
    | zero => simp [digits,List.range_succ,branchOutput,Allowed,digitCode]
    | succ D =>
      cases D with
      | zero => simp [digits,List.range_succ,branchOutput,Allowed,digitCode]
      | succ D => simp [digits,List.range_succ,branchOutput,Allowed,digitCode,
          show 1 ≤ D+2 by omega,show 2 ≤ D+2 by omega,List.append_assoc]
end ThreeSum.LightTernaryNearEnumeration

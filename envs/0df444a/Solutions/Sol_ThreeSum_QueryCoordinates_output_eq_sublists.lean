-- Prove2me | solution 1 for ThreeSum.QueryCoordinates.output_eq_sublists
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:49:14.235975+00:00
-- url     : https://prove2.me/submissions/cd348c99-0090-4b99-a519-2ef1fe4ab76d

import Definitions.Def_Submission_ThreeSum_LightWeightedEnumeration
import Definitions.Def_Submission_ThreeSum_MaskDifference
import Definitions.Def_Submission_ThreeSum_MaskDecode
import Mathlib.Data.List.Sublists
import Mathlib.Algebra.BigOperators.Fin
import Definitions.Def_Submission_ThreeSum_QueryCoordinates
import Theorems.Thm_ThreeSum_QueryCoordinates_positions_zero
import Theorems.Thm_ThreeSum_QueryCoordinates_mem_positions
import Theorems.Thm_ThreeSum_QueryCoordinates_positions_toFinset
import Theorems.Thm_ThreeSum_QueryCoordinates_positions_length
import Theorems.Thm_ThreeSum_QueryCoordinates_selectedPowers_length
import Theorems.Thm_ThreeSum_QueryCoordinates_selectedPowers_zero
import Theorems.Thm_ThreeSum_QueryCoordinates_selectedPowers_sum
import Theorems.Thm_ThreeSum_QueryCoordinates_total_weights
import Theorems.Thm_ThreeSum_QueryCoordinates_setLayer_length
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_output_empty
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_output_length
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_output_succ
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_output_zero
import Theorems.Thm_ThreeSum_LightWeightedEnumeration_output_empty
import Theorems.Thm_ThreeSum_LightWeightedEnumeration_output_length
import Theorems.Thm_ThreeSum_LightWeightedEnumeration_output_succ
import Theorems.Thm_ThreeSum_LightWeightedEnumeration_output_zero
import Theorems.Thm_ThreeSum_LightWeightedEnumeration_total_succ
import Theorems.Thm_ThreeSum_LightWeightedEnumeration_total_zero
import Theorems.Thm_ThreeSum_MaskDifference_subsetMask_empty
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
attribute [local simp] ThreeSum.LightWeightedEnumeration.output_length
attribute [local simp] ThreeSum.LightWeightedEnumeration.output_zero
attribute [local simp] ThreeSum.LightWeightedEnumeration.total_succ
attribute [local simp] ThreeSum.LightWeightedEnumeration.total_zero
attribute [local simp] ThreeSum.MaskDifference.subsetMask_empty
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero


attribute [local simp] ThreeSum.QueryCoordinates.positions_zero
attribute [local simp] ThreeSum.QueryCoordinates.mem_positions
attribute [local simp] ThreeSum.QueryCoordinates.positions_toFinset
attribute [local simp] ThreeSum.QueryCoordinates.positions_length
attribute [local simp] ThreeSum.QueryCoordinates.selectedPowers_length
attribute [local simp] ThreeSum.QueryCoordinates.selectedPowers_zero
attribute [local simp] ThreeSum.QueryCoordinates.selectedPowers_sum
attribute [local simp] ThreeSum.QueryCoordinates.total_weights
attribute [local simp] ThreeSum.QueryCoordinates.setLayer_length

set_option autoImplicit false
open ThreeSum ThreeSum.QueryCoordinates
open Finset ThreeSum.SubsetAddress
open scoped BigOperators
namespace ThreeSum.QueryCoordinates
theorem _root_.solution (weight : ℕ → ℕ) (L k pref : ℕ) :
    LightWeightedEnumeration.output weight L k pref =
      (((List.range L).reverse).sublistsLen k).map
        (fun xs => ((pref+(xs.map weight).sum : ℕ) : ℤ)) := by
  induction L generalizing k pref with
  | zero => cases k <;> simp [LightWeightedEnumeration.output]
  | succ L ih =>
    cases k with
    | zero => simp [LightWeightedEnumeration.output]
    | succ k =>
      by_cases hk : k+1 ≤ L+1
      · rw [LightWeightedEnumeration.output_succ hk,ih,ih]
        simp [List.range_succ,List.reverse_append,List.sublistsLen_succ_cons,
          List.map_append,List.map_map,Function.comp_def,Nat.add_assoc]
      · rw [LightWeightedEnumeration.output_empty (by omega),List.sublistsLen_of_length_lt]
        · rfl
        · simp only [List.length_reverse,List.length_range]; omega
end ThreeSum.QueryCoordinates

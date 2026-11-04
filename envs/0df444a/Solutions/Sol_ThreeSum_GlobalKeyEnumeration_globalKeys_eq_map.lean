-- Prove2me | solution 1 for ThreeSum.GlobalKeyEnumeration.globalKeys_eq_map
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:16:30.90954+00:00
-- url     : https://prove2.me/submissions/042a11f1-8ad7-4a82-97c3-a175e91f6142

import Definitions.Def_Submission_ThreeSum_RadixKeyLists
import Definitions.Def_Submission_ThreeSum_LocalMaskGraph
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.ProdSigma
import Definitions.Def_Submission_ThreeSum_GlobalKeyEnumeration
import Theorems.Thm_ThreeSum_GlobalKeyEnumeration_ofFn_tupleOfList
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Theorems.Thm_ThreeSum_RadixKeyLists_values_eq_map
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
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero



set_option autoImplicit false
open ThreeSum ThreeSum.GlobalKeyEnumeration
open GlobalEncoding LocalGraph LocalCoverBounds LocalHashMoments
open RadixKeyLists
open scoped BigOperators
set_option maxHeartbeats 1800000
namespace ThreeSum.GlobalKeyEnumeration
theorem _root_.solution (h J : ℕ) :
    globalKeys h J=(globalRecords h J).map globalKey := by
  rw [globalKeys,localKeys,values_eq_map]
  unfold globalRecords
  rw [List.map_map]
  symm
  calc
    _ = (tuples (localRecords h) J).attach.map
        (fun xs => Radix.positionalHash (localPrime h) blockKey xs.val) := by
      apply List.map_congr_left
      intro xs _
      simp only [Function.comp_def,globalKey,ofFn_tupleOfList]
    _ = _ := by simp
end ThreeSum.GlobalKeyEnumeration

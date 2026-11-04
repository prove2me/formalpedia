-- Prove2me | solution 1 for ThreeSum.GlobalKeyEnumeration.globalRecords_nodup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:39:10.549918+00:00
-- url     : https://prove2.me/submissions/6a9d7f51-4409-49c7-8380-3fa628688eb8

import Definitions.Def_Submission_ThreeSum_RadixKeyLists
import Definitions.Def_Submission_ThreeSum_LocalMaskGraph
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.ProdSigma
import Definitions.Def_Submission_ThreeSum_GlobalKeyEnumeration
import Theorems.Thm_ThreeSum_GlobalKeyEnumeration_localRecords_nodup
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
import Definitions.Def_WeightedCache3SUM_Alias_03e0bdb6c4745899
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
theorem _root_.solution (h J : ℕ) : (globalRecords h J).Nodup := by
  apply ((tuples_nodup _ (localRecords_nodup h) J).attach).map
  intro xs ys he
  apply Subtype.ext
  have he' := congrArg List.ofFn he
  simpa only [ofFn_tupleOfList] using he'
end ThreeSum.GlobalKeyEnumeration

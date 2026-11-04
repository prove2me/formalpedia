-- Prove2me | solution 1 for ThreeSum.OutputDecodeOrder.tuples_succ_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:34:46.368199+00:00
-- url     : https://prove2.me/submissions/116b0204-acc2-45cd-bc74-c9d34c13b145

import Definitions.Def_Submission_ThreeSum_RadixKeyLists
import Definitions.Def_Submission_ThreeSum_GlobalKeyEnumeration
import Definitions.Def_Submission_ThreeSumApsp_Util_List
import Definitions.Def_Submission_ThreeSum_OutputDecodeOrder
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
open ThreeSum ThreeSum.OutputDecodeOrder
open RadixKeyLists
set_option maxHeartbeats 1800000
set_option maxRecDepth 6000
variable {α β : Type*}
namespace ThreeSum.OutputDecodeOrder
theorem _root_.solution (base : List α) (J : ℕ) :
    tuples base (J+1) = (tuples base J).flatMap fun xs => base.map fun a => xs++[a] := by
  induction J with
  | zero =>
    have hh : base.flatMap (fun a => [[a]]) = base.map (fun a => [a]) := by
      induction base with
      | nil => rfl
      | cons a xs ih => simp [ih]
    simpa [tuples] using hh
  | succ J ih =>
    calc
      _ = base.flatMap (fun a => (tuples base (J+1)).map (List.cons a)) := rfl
      _ = base.flatMap (fun a => ((tuples base J).flatMap
          (fun xs => base.map (fun b => xs++[b]))).map (List.cons a)) := by rw [ih]
      _ = (base.flatMap (fun a => (tuples base J).map (List.cons a))).flatMap
          (fun xs => base.map (fun a => xs++[a])) := by
        simp only [List.map_flatMap,List.flatMap_assoc,List.flatMap_map,List.map_map,Function.comp_def,
          List.cons_append]
      _ = _ := rfl
end ThreeSum.OutputDecodeOrder

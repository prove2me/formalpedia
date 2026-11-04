-- Prove2me | solution 1 for ThreeSum.TernaryFixedDictionaries.trimmed_records_of_retained
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:42:00.956527+00:00
-- url     : https://prove2.me/submissions/16b4ca9d-b0ad-4a88-b0ee-0d4993c85a77

import Definitions.Def_Submission_ThreeSum_TernaryGlobalEncoding
import Definitions.Def_Submission_ThreeSum_LightFixedRadixDictionary
import Definitions.Def_Submission_ThreeSum_TernaryFixedDictionaries
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
import Theorems.Thm_ThreeSum_LocalGraph_left_mem_vertices
import Theorems.Thm_ThreeSum_LocalGraph_right_mem_vertices
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_zero
import Theorems.Thm_ThreeSum_SubsetAddress_natPositions_card
import Theorems.Thm_ThreeSum_SubsetAddress_weight_zero
import Theorems.Thm_ThreeSum_TernaryCoverLocal_left_mem_vertices
import Theorems.Thm_ThreeSum_TernaryCoverLocal_right_mem_vertices
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
noncomputable section
open ThreeSum ThreeSum.TernaryFixedDictionaries
open Finset TernaryJointType TernaryCoverLocal TernaryGlobalEncoding RadixKeyLists Light
variable {L p : ℕ} [Fact p.Prime] {α π : DigitType}
variable {I : Type*} [Fintype I] [DecidableEq I]
namespace ThreeSum.TernaryFixedDictionaries
theorem _root_.solution {Ω : Type*}
    (maps : I → TernaryCoverHashes.Coordinate (Fin L) → ZMod p) (B : ℕ)
    (occ : Ω → I) (edge : Ω → LocalEdge L α π) (c : Ω)
    (hleft : TernaryCoverTrimming.bucketSize (fieldVertices L p α) TernaryCoverHashes.leftVector
      (maps (occ c)) (leftHash (maps (occ c)) (edge c)) ≤ B)
    (hright : TernaryCoverTrimming.bucketSize (fieldVertices L p α) TernaryCoverHashes.rightVector
      (maps (occ c)) (rightHash (maps (occ c)) (edge c)) ≤ B) :
    ∃ rL rR : SourceRecord L α I,
      rL ∈ trimmedLeftRecords maps B ∧ rR ∈ trimmedRightRecords maps B ∧
      leftKey maps rL = rawLeft maps occ edge c ∧ rightKey maps rR = rawRight maps occ edge c := by
  classical
  refine ⟨(occ c,⟨left (edge c),left_mem_vertices _⟩),
    (occ c,⟨right (edge c),right_mem_vertices _⟩), ?_, ?_, rfl, rfl⟩
  · simpa [trimmedLeftRecords,acceptedLeft,leftNative,leftHash,fieldLeft] using hleft
  · simpa [trimmedRightRecords,acceptedRight,rightNative,rightHash,fieldRight] using hright
end ThreeSum.TernaryFixedDictionaries

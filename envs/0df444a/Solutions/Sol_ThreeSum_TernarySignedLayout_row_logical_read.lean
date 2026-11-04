-- Prove2me | solution 1 for ThreeSum.TernarySignedLayout.row_logical_read
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:26:42.353738+00:00
-- url     : https://prove2.me/submissions/91ce9aa2-b67f-4978-b172-8502e0cf374a

import Definitions.Def_Submission_ThreeSum_LightTernarySignedRow
import Definitions.Def_Submission_ThreeSum_TernarySignedLayout
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
import Theorems.Thm_ThreeSum_TernarySignedDigits_carryNat_zero
import Theorems.Thm_ThreeSum_TernarySignedReduction_mem_carryCatalog
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
attribute [local simp] ThreeSum.TernarySignedDigits.carryNat_zero
attribute [local simp] ThreeSum.TernarySignedReduction.mem_carryCatalog



set_option autoImplicit false
open ThreeSum ThreeSum.TernarySignedLayout
open TernarySignedReduction
namespace ThreeSum.TernarySignedLayout
theorem _root_.solution {μ : ℕ→ℤ} {dst J : ℕ} {f : Coordinate J→ℤ}
    (hrow : LightTernarySignedRow.Row μ dst J f) {i : ℕ} (hi : i<J+2) :
    μ (dst+offset J i)=feature f i := by
  by_cases hd : i<J
  · have he : dst+(J-1-i)=dst+J-1-i := by omega
    simp only [offset,if_pos hd,feature,dif_pos hd,he]
    exact hrow.1 ⟨i,hd⟩
  · by_cases hz : i=J
    · subst i
      simpa [offset,feature] using hrow.2.1
    · have he : i=J+1 := by omega
      subst i
      simpa [offset,feature,Nat.add_assoc] using hrow.2.2
end ThreeSum.TernarySignedLayout

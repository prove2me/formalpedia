-- Prove2me | solution 1 for ThreeSum.LightExtensionMenuMatrix.cell_word_after_ctx
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:46:11.941205+00:00
-- url     : https://prove2.me/submissions/f0c38c5f-a554-4880-93bb-bb0f84d4fdd0

import Definitions.Def_Submission_ThreeSum_LightExtensionMenuMatrix
import Definitions.Def_Submission_ThreeSum_LightExtensionMenuBudget
import Theorems.Thm_ThreeSum_LightExtensionMenuMatrix_cell_word_polynomial
import Theorems.Thm_ThreeSum_LightExtensionMenuMatrix_cell_word_affine_ctx
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
import Theorems.Thm_ThreeSum_LightPolynomialCoefficient_raw_zero
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
attribute [local simp] ThreeSum.LightPolynomialCoefficient.raw_zero
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero
attribute [local simp] ThreeSum.TernarySignedDigits.carryNat_zero
attribute [local simp] ThreeSum.TernarySignedReduction.mem_carryCatalog



set_option autoImplicit false
open ThreeSum ThreeSum.LightExtensionMenuMatrix
set_option maxHeartbeats 3000000
namespace ThreeSum.LightExtensionMenuMatrix
theorem _root_.solution (C : LightExtensionQuotientPredicate.Layout) (q ctx : ℕ)
    (hsize : C.p^C.dim=q) :
    LightExtensionMultiplyCell.word C q ctx ≤ ctx+1000000*(C.dim+C.p+q+2)^4 := by
  rw [cell_word_affine_ctx]
  apply Nat.add_le_add_left
  simpa using cell_word_polynomial C q 0 hsize
end ThreeSum.LightExtensionMenuMatrix

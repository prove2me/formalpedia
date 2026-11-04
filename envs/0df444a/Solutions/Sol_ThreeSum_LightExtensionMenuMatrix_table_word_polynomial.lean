-- Prove2me | solution 1 for ThreeSum.LightExtensionMenuMatrix.table_word_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:51:22.400188+00:00
-- url     : https://prove2.me/submissions/5009f2c1-237d-4da8-9a07-e4285f1c30e9

import Definitions.Def_Submission_ThreeSum_LightExtensionMenuMatrix
import Definitions.Def_Submission_ThreeSum_LightExtensionMenuBudget
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
theorem _root_.solution (q ctx p dim powers a b : ℕ) :
    LightExtensionMultiplyTable.word q ctx p dim powers a b ≤
      100000*(q+ctx+p+dim+powers+a+b+2)^2 := by
  let B := q+ctx+p+dim+powers+a+b+2
  have hB : 1 ≤ B := by dsimp [B]; omega
  have hq : q ≤ B := by dsimp [B]; omega
  have hctx : ctx ≤ B := by dsimp [B]; omega
  have hp : p ≤ B := by dsimp [B]; omega
  have hd : dim ≤ B := by dsimp [B]; omega
  have hpw : powers ≤ B := by dsimp [B]; omega
  have ha : a ≤ B := by dsimp [B]; omega
  have hb : b ≤ B := by dsimp [B]; omega
  have hm : LightExtensionMultiplyTable.word q ctx p dim powers a b ≤
      LightExtensionMultiplyTable.word B B B B B B B := by
    unfold LightExtensionMultiplyTable.word
    gcongr
  apply hm.trans
  change LightExtensionMultiplyTable.word B B B B B B B ≤ 100000*B^2
  have h0 : 1 ≤ B^2 := Nat.one_le_pow _ _ hB
  have h1 : B ≤ B^2 := by simpa using Nat.pow_le_pow_right hB (show 1 ≤ 2 by decide)
  unfold LightExtensionMultiplyTable.word
  ring_nf
  omega
end ThreeSum.LightExtensionMenuMatrix

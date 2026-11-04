-- Prove2me | solution 1 for ThreeSum.LightExtensionBackendLayout.end_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:00:31.672374+00:00
-- url     : https://prove2.me/submissions/1dc0c7e4-4c1c-4ab6-9b30-26a73b4f0d17

import Definitions.Def_Submission_ThreeSum_LightExtensionBackend
import Definitions.Def_Submission_ThreeSum_LightExtensionMenuBudget
import Definitions.Def_Submission_ThreeSum_LightIrreducibleBudget
import Definitions.Def_Submission_ThreeSum_LightExtensionBackendLayout
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
import Theorems.Thm_ThreeSum_LightIrreducibleFinder_program_length
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
attribute [local simp] ThreeSum.LightIrreducibleFinder.program_length
attribute [local simp] ThreeSum.LightPolynomialCoefficient.raw_zero
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero
attribute [local simp] ThreeSum.TernarySignedDigits.carryNat_zero
attribute [local simp] ThreeSum.TernarySignedReduction.mem_carryCatalog



set_option autoImplicit false
open ThreeSum ThreeSum.LightExtensionBackendLayout
open Light
set_option maxHeartbeats 6000000
set_option maxRecDepth 10000
namespace ThreeSum.LightExtensionBackendLayout
theorem _root_.solution (base d p q J : ℕ) : sum base d q J+2*d≤base+reserve d p q J := by
  let B := params d p q J
  have hB : 1≤B := by dsimp [B,params]; omega
  have hd : d≤B := by dsimp [B,params]; omega
  have hq : q≤B := by dsimp [B,params]; omega
  have hJ : J≤B := by dsimp [B,params]; omega
  have he : sum base d q J+2*d=base+(13*d+11+q*q+2*q*q*(J+2)) := by
    unfold sum prod r h b a physical logical table ctx target
    ring
  rw [he]
  apply Nat.add_le_add_left
  have hm : 13*d+11+q*q+2*q*q*(J+2)≤13*B+11+B*B+2*B*B*(B+2) := by gcongr
  apply hm.trans
  change 13*B+11+B*B+2*B*B*(B+2)≤100000000*B^6
  have h0 : 1≤B^6 := Nat.one_le_pow _ _ hB
  have h1 : B≤B^6 := by simpa using Nat.pow_le_pow_right hB (show 1≤6 by decide)
  have h2 : B^2≤B^6 := Nat.pow_le_pow_right hB (by decide)
  have h3 : B^3≤B^6 := Nat.pow_le_pow_right hB (by decide)
  ring_nf
  omega
end ThreeSum.LightExtensionBackendLayout

-- Prove2me | solution 1 for ThreeSum.LightExtensionBackend.time_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:47:07.737856+00:00
-- url     : https://prove2.me/submissions/5a7422f2-6737-4534-9889-6f1c20fd156c

import Definitions.Def_Submission_ThreeSum_LightExtensionBackend
import Definitions.Def_Submission_ThreeSum_LightIrreducibleBudget
import Definitions.Def_Submission_ThreeSum_LightExtensionMenuBudget
import Definitions.Def_Submission_ThreeSum_LightExtensionBackendBudget
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
import Theorems.Thm_ThreeSum_LightExtensionMenuMatrix_time_polynomial
import Theorems.Thm_ThreeSum_LightIrreducibleFinder_program_length
import Theorems.Thm_ThreeSum_LightIrreducibleFinder_setupTime_polynomial
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
open ThreeSum ThreeSum.LightExtensionBackend
set_option maxHeartbeats 2000000
namespace ThreeSum.LightExtensionBackend
theorem _root_.solution (F : LightExtensionFactorPredicate.Layout)
    (q J a b h r prod sum : ℕ) :
    time F q J a b h r prod sum (LightIrreducibleFinder.uniformFactorTime F.dim F.p q) ≤
      10000000000*(F.dim+F.p+q+J+2)^10 := by
  let B := F.dim+F.p+q+J+2
  have hB : 1 ≤ B := by dsimp [B]; omega
  have hsmall : F.dim+F.p+q+2 ≤ B := by dsimp [B]; omega
  have hf := LightIrreducibleFinder.setupTime_polynomial F q
  have hf' : LightIrreducibleFinder.setupTime F q (LightIrreducibleFinder.uniformFactorTime F.dim F.p q) ≤
      1000000000*B^10 := hf.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hsmall 10))
  have hm := LightExtensionMenuMatrix.time_polynomial (quotientLayout F a b h r prod sum) q J
  have hm' : LightExtensionMenuMatrix.time (quotientLayout F a b h r prod sum) q J ≤
      1000000000*B^8 := by simpa only [quotientLayout] using hm
  have hp : B^8 ≤ B^10 := Nat.pow_le_pow_right hB (by decide)
  have h1 : 1 ≤ B^10 := Nat.one_le_pow _ _ hB
  unfold time
  change _ ≤ 10000000000*B^10
  omega
end ThreeSum.LightExtensionBackend

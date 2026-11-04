-- Prove2me | solution 1 for ThreeSum.LightExtensionMenuMatrix.time_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:38:27.823365+00:00
-- url     : https://prove2.me/submissions/1c25145f-7531-4926-92af-aa1d161cef84

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
theorem _root_.solution (C : LightExtensionQuotientPredicate.Layout) (q J : ℕ) :
    time C q J ≤ 1000000000*(C.dim+C.p+q+J+2)^8 := by
  let B := C.dim+C.p+q+J+2
  let D : LightExtensionQuotientPredicate.Layout := { C with p := B, dim := B }
  have hB : 1 ≤ B := by dsimp [B]; omega
  have hd : C.dim ≤ B := by dsimp [B]; omega
  have hp : C.p ≤ B := by dsimp [B]; omega
  have hq : q ≤ B := by dsimp [B]; omega
  have hJ : J ≤ B := by dsimp [B]; omega
  have hm : time C q J ≤ time D B B := by
    unfold time LightExtensionMultiplyTable.time LightExtensionMultiplyCell.time
      LightExtensionMultiplyCell.searchTime LightExtensionQuotientPredicate.time
      LightCoefficientDecode.time LightRadixDigit.time LightPolynomialQuotientCheck.time
      LightPolynomialProductArray.time LightPolynomialProductCheck.time
      LightPolynomialCoefficient.reducedTime LightPolynomialCoefficient.time
      LightPrimeAddArray.time LightPrimeCoefficient.mulAddTime LightExtensionSeedMatrix.time
      LightExtensionSeedRow.time LightSignedCoefficientMatrix.time LightSignedCoefficientLayout.time LightRadixDigit.time
    dsimp only [D]
    gcongr
  apply hm.trans
  change time D B B ≤ 1000000000*B^8
  have h0 : 1 ≤ B^8 := Nat.one_le_pow _ _ hB
  have h1 : B ≤ B^8 := by simpa using Nat.pow_le_pow_right hB (show 1 ≤ 8 by decide)
  have h2 : B^2 ≤ B^8 := Nat.pow_le_pow_right hB (by decide)
  have h3 : B^3 ≤ B^8 := Nat.pow_le_pow_right hB (by decide)
  have h4 : B^4 ≤ B^8 := Nat.pow_le_pow_right hB (by decide)
  have h5 : B^5 ≤ B^8 := Nat.pow_le_pow_right hB (by decide)
  have h6 : B^6 ≤ B^8 := Nat.pow_le_pow_right hB (by decide)
  have h7 : B^7 ≤ B^8 := Nat.pow_le_pow_right hB (by decide)
  unfold time LightExtensionMultiplyTable.time LightExtensionMultiplyCell.time
    LightExtensionMultiplyCell.searchTime LightExtensionQuotientPredicate.time
    LightCoefficientDecode.time LightRadixDigit.time LightPolynomialQuotientCheck.time
    LightPolynomialProductArray.time LightPolynomialProductCheck.time
    LightPolynomialCoefficient.reducedTime LightPolynomialCoefficient.time
    LightPrimeAddArray.time LightPrimeCoefficient.mulAddTime LightExtensionSeedMatrix.time
    LightExtensionSeedRow.time LightSignedCoefficientMatrix.time LightSignedCoefficientLayout.time LightRadixDigit.time
  dsimp only [D]
  ring_nf
  omega
end ThreeSum.LightExtensionMenuMatrix

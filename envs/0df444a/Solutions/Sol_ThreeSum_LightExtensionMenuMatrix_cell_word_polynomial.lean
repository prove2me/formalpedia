-- Prove2me | solution 1 for ThreeSum.LightExtensionMenuMatrix.cell_word_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:40:40.379515+00:00
-- url     : https://prove2.me/submissions/6eb8e436-0a5e-446b-ab60-c841141c54ef

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
theorem _root_.solution (C : LightExtensionQuotientPredicate.Layout) (q ctx : ℕ)
    (hsize : C.p^C.dim=q) :
    LightExtensionMultiplyCell.word C q ctx ≤ 1000000*(C.dim+C.p+q+ctx+2)^4 := by
  let B := C.dim+C.p+q+ctx+2
  have hB : 1 ≤ B := by dsimp [B]; omega
  have hd : C.dim ≤ B := by dsimp [B]; omega
  have hp : C.p ≤ B := by dsimp [B]; omega
  have hq : q ≤ B := by dsimp [B]; omega
  have hctx : ctx ≤ B := by dsimp [B]; omega
  have hpow1 : C.p^(C.dim+1)=q*C.p := by rw [pow_succ,hsize]
  have hpow2 : C.p^(2*C.dim+1)=q*q*C.p := by
    rw [show 2*C.dim+1=C.dim+C.dim+1 by omega,pow_succ,pow_add,hsize]
  let E := fun d p q ctx : ℕ =>
    8*(q+q*p+p+d+3)+4*(q+q*q*p+p+2*d+3)+
    100*((d+2)*(p+1)^2+4*d+p+20)+100+4*(q*q+q+3)+q*q+q+ctx+100
  have he : LightExtensionMultiplyCell.word C q ctx=E C.dim C.p q ctx := by
    unfold LightExtensionMultiplyCell.word LightExtensionQuotientPredicate.word
      LightCoefficientDecode.word LightPolynomialQuotientCheck.word LightRadixDigit.word E
    rw [hpow1,hpow2]
    ring
  rw [he]
  have hm : E C.dim C.p q ctx ≤ E B B B B := by unfold E; gcongr
  apply hm.trans
  change E B B B B ≤ 1000000*B^4
  have h0 : 1 ≤ B^4 := Nat.one_le_pow _ _ hB
  have h1 : B ≤ B^4 := by simpa using Nat.pow_le_pow_right hB (show 1 ≤ 4 by decide)
  have h2 : B^2 ≤ B^4 := Nat.pow_le_pow_right hB (by decide)
  have h3 : B^3 ≤ B^4 := Nat.pow_le_pow_right hB (by decide)
  unfold E
  ring_nf
  omega
end ThreeSum.LightExtensionMenuMatrix

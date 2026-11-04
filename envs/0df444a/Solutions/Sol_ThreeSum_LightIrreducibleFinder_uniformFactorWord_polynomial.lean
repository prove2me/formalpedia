-- Prove2me | solution 1 for ThreeSum.LightIrreducibleFinder.uniformFactorWord_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:41:15.633208+00:00
-- url     : https://prove2.me/submissions/f6afdb8d-53d9-4779-8845-d56f964c064e

import Definitions.Def_Submission_ThreeSum_LightIrreducibleFinder
import Definitions.Def_Submission_ThreeSum_LightIrreducibleBudget
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



set_option autoImplicit false
open ThreeSum ThreeSum.LightIrreducibleFinder
open Light
set_option maxHeartbeats 3000000
namespace ThreeSum.LightIrreducibleFinder
theorem _root_.solution (d p q : ℕ) (hsize : p^d=q) :
    uniformFactorWord d p q ≤ 1000000*(d+p+q+2)^4 := by
  let B := d+p+q+2
  have hB : 1 ≤ B := by dsimp [B]; omega
  have hd : d ≤ B := by dsimp [B]; omega
  have hp : p ≤ B := by dsimp [B]; omega
  have hq : q ≤ B := by dsimp [B]; omega
  have hpow : p^(2*d+1)=q*q*p := by
    rw [show 2*d+1=d+d+1 by omega,pow_succ,pow_add,hsize]
  let E := fun d p q : ℕ => 8*(2*q+q*q*p+p+2*d+3)+20*((d+2)*(p+1)^2+3*d+11)+200
  have he : uniformFactorWord d p q=E d p q := by
    unfold uniformFactorWord LightCoefficientDecode.word E
    rw [hpow]
    ring
  rw [he]
  have hm : E d p q ≤ E B B B := by unfold E; gcongr
  apply hm.trans
  change E B B B ≤ 1000000*B^4
  have h0 : 1 ≤ B^4 := Nat.one_le_pow _ _ hB
  have h1 : B ≤ B^4 := by simpa using Nat.pow_le_pow_right hB (show 1 ≤ 4 by decide)
  have h2 : B^2 ≤ B^4 := Nat.pow_le_pow_right hB (by decide)
  have h3 : B^3 ≤ B^4 := Nat.pow_le_pow_right hB (by decide)
  unfold E
  ring_nf
  omega
end ThreeSum.LightIrreducibleFinder

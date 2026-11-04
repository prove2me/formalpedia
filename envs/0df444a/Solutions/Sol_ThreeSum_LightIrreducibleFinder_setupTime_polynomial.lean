-- Prove2me | solution 1 for ThreeSum.LightIrreducibleFinder.setupTime_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:41:14.453959+00:00
-- url     : https://prove2.me/submissions/16c383e9-f0b7-42a1-9c10-a7c9f6f0f476

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
theorem _root_.solution (C : LightExtensionFactorPredicate.Layout) (q : ℕ) :
    setupTime C q (uniformFactorTime C.dim C.p q) ≤ 1000000000*(C.dim+C.p+q+2)^10 := by
  let B := C.dim+C.p+q+2
  let D : LightExtensionFactorPredicate.Layout := {C with dim := B,p := B}
  have hB : 1 ≤ B := by dsimp [B]; omega
  have hd : C.dim ≤ B := by dsimp [B]; omega
  have hp : C.p ≤ B := by dsimp [B]; omega
  have hq : q ≤ B := by dsimp [B]; omega
  have hm : setupTime C q (uniformFactorTime C.dim C.p q) ≤ setupTime D B (uniformFactorTime B B B) := by
    unfold setupTime searchTime candidateTime degreeTime uniformFactorTime powTableTime
      LightCoefficientDecode.time LightPolynomialProductCheck.time
      LightPolynomialCoefficient.reducedTime LightPolynomialCoefficient.time LightRadixDigit.time
    dsimp only [D]
    gcongr
  apply hm.trans
  change setupTime D B (uniformFactorTime B B B) ≤ 1000000000*B^10
  have h0 : 1 ≤ B^10 := Nat.one_le_pow _ _ hB
  have h1 : B ≤ B^10 := by simpa using Nat.pow_le_pow_right hB (show 1 ≤ 10 by decide)
  have h2 : B^2 ≤ B^10 := Nat.pow_le_pow_right hB (by decide)
  have h3 : B^3 ≤ B^10 := Nat.pow_le_pow_right hB (by decide)
  have h4 : B^4 ≤ B^10 := Nat.pow_le_pow_right hB (by decide)
  have h5 : B^5 ≤ B^10 := Nat.pow_le_pow_right hB (by decide)
  have h6 : B^6 ≤ B^10 := Nat.pow_le_pow_right hB (by decide)
  have h7 : B^7 ≤ B^10 := Nat.pow_le_pow_right hB (by decide)
  have h8 : B^8 ≤ B^10 := Nat.pow_le_pow_right hB (by decide)
  have h9 : B^9 ≤ B^10 := Nat.pow_le_pow_right hB (by decide)
  have hupper : setupTime D B (uniformFactorTime B B B) ≤
      17*(2*B+1)+8+
      (B*(LightCoefficientDecode.time (2*B) (2*B)+
        (B*(uniformFactorTime B B B+200)+100)+200+200)+100)+
      LightCoefficientDecode.time (2*B) (2*B)+300 := by
    unfold setupTime searchTime candidateTime degreeTime powTableTime
    dsimp only [D]
    gcongr
    exact Nat.sub_le _ _
  apply hupper.trans
  unfold uniformFactorTime LightCoefficientDecode.time LightPolynomialProductCheck.time
    LightPolynomialCoefficient.reducedTime LightPolynomialCoefficient.time LightRadixDigit.time
  ring_nf
  omega
end ThreeSum.LightIrreducibleFinder

-- Prove2me | solution 1 for ThreeSum.LightExtensionMenuMatrix.signed_physical_hash
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:51:05.179246+00:00
-- url     : https://prove2.me/submissions/5d0146ad-958f-43b8-be28-33f49074d272

import Definitions.Def_Submission_ThreeSum_LightExtensionFieldMultiply
import Definitions.Def_Submission_ThreeSum_LightExtensionMenuMatrix
import Definitions.Def_Submission_ThreeSum_LightExtensionMenuSemantics
import Theorems.Thm_ThreeSum_LightExtensionMenuMatrix_dot_offset
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
import Theorems.Thm_ThreeSum_TernaryExtensionEncoding_naturalDot_rowMenu
import Theorems.Thm_ThreeSum_TernaryExtensionEncoding_signed_lift_cast
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
noncomputable section
open ThreeSum ThreeSum.LightExtensionMenuMatrix
open TernaryExtensionEncoding
set_option maxHeartbeats 2000000
variable {p : ℕ} [Fact p.Prime] {f : Polynomial (ZMod p)}
variable [Fact (Irreducible f)] [Fintype (AdjoinRoot f)]
namespace ThreeSum.LightExtensionMenuMatrix
theorem _root_.solution (hf : f.Monic) (hd : 0 < f.natDegree)
    (J : ℕ) (x y : AdjoinRoot f) (raw : ℕ → ℤ)
    (hlift : ∀ i < J+2, 0 ≤ (p : ℤ)+raw i) :
    LightNaturalDot.dot
      (fun i => LightExtensionSeedRow.trajectory (encodedMul hf) (encode hf x) (encode hf y)
        (TernarySignedLayout.offset J i)%p)
      (fun i => ((p : ℤ)+raw (TernarySignedLayout.offset J i)).toNat) (J+2)%p=
      (TernaryOriginalRowMenu.row (J+2) (constantCoefficient hf hd) (x,y)
        (fun i => (raw i.val : ZMod p))).val := by
  rw [dot_offset J
    (fun i => LightExtensionSeedRow.trajectory (encodedMul hf) (encode hf x) (encode hf y) i%p)
    (fun i => ((p : ℤ)+raw i).toNat)]
  have hcomm : LightNaturalDot.dot
      (fun i => LightExtensionSeedRow.trajectory (encodedMul hf) (encode hf x) (encode hf y) i%p)
      (fun i => ((p : ℤ)+raw i).toNat) (J+2)=
    LightNaturalDot.dot (fun i => ((p : ℤ)+raw i).toNat)
      (fun i => LightExtensionSeedRow.trajectory (encodedMul hf) (encode hf x) (encode hf y) i%p) (J+2) := by
    unfold LightNaturalDot.dot LightBooleanDot.dot
    apply Finset.sum_congr rfl
    intro i hi
    exact Nat.mul_comm _ _
  rw [hcomm]
  apply naturalDot_rowMenu hf hd (J+2) x y (fun i => raw i.val)
  · intro i
    have h := signed_lift_cast (p := p) (raw i.val) (by simpa [add_comm] using hlift i.val i.isLt)
    simpa [add_comm] using h
  · intro i
    rfl
end ThreeSum.LightExtensionMenuMatrix

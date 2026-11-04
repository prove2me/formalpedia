-- Prove2me | solution 1 for ThreeSum.TernaryExtensionEncoding.physical_original_hash
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:20:04.140821+00:00
-- url     : https://prove2.me/submissions/4b6f1c49-4018-4f3c-a849-9bb9d286561c

import Definitions.Def_Submission_ThreeSum_TernaryExtensionSeedSemantics
import Definitions.Def_Submission_ThreeSum_LightTernaryAppendKeys
import Definitions.Def_Submission_ThreeSum_TernarySignedLayout
import Definitions.Def_Submission_ThreeSum_TernaryOriginalKeyCodes
import Theorems.Thm_ThreeSum_TernaryExtensionEncoding_physical_dot_eq_logical
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
import Theorems.Thm_ThreeSum_TernaryExtensionEncoding_signed_lift_cast
import Theorems.Thm_ThreeSum_TernaryOriginalRowMenu_row_eq_dot
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
open ThreeSum ThreeSum.TernaryExtensionEncoding
open Polynomial Finset
open scoped BigOperators
variable {p : ℕ} [Fact p.Prime]
set_option maxHeartbeats 3000000
variable {f : (ZMod p)[X]} [Fact (Irreducible f)] [Fintype (AdjoinRoot f)]
namespace ThreeSum.TernaryExtensionEncoding
theorem _root_.solution (hf : f.Monic) (hd : 0<f.natDegree) (J : ℕ)
    (x y : AdjoinRoot f) (raw : Fin (J+2) → ℤ) (z : ℕ → ℤ) (c : ℕ → ℕ)
    (hz : ∀ i : Fin (J+2), z i.val=raw (digitOrder J i))
    (hzNonneg : ∀ i<J+2, 0≤(p : ℤ)+z i)
    (hc : ∀ i : Fin (J+2), c i.val=
      (TernaryOriginalRowMenu.seedRow (J+2) (constantCoefficient hf hd) (x,y) (digitOrder J i)).val) :
    LightNaturalDot.dot c (fun k => LightSignedRowHash.lifted p (z k)) (J+2)%p=
      (TernaryOriginalRowMenu.row (J+2) (constantCoefficient hf hd) (x,y)
        (fun i => (raw i : ZMod p))).val := by
  have he : ((LightNaturalDot.dot c (fun k => LightSignedRowHash.lifted p (z k)) (J+2) : ℕ) : ZMod p)=
      TernaryOriginalRowMenu.row (J+2) (constantCoefficient hf hd) (x,y)
        (fun i => (raw i : ZMod p)) := by
    rw [TernaryOriginalRowMenu.row_eq_dot]
    unfold LightNaturalDot.dot LightBooleanDot.dot
    rw [Nat.cast_sum,← Fin.sum_univ_eq_sum_range]
    calc
      _ = ∑ i : Fin (J+2), (raw (digitOrder J i) : ZMod p)*
          TernaryOriginalRowMenu.seedRow (J+2) (constantCoefficient hf hd) (x,y) (digitOrder J i) := by
        apply sum_congr rfl
        intro i hi
        rw [Nat.cast_mul,hc i,ZMod.natCast_zmod_val]
        have hlift : ((LightSignedRowHash.lifted p (z i.val) : ℕ) : ZMod p)=(raw (digitOrder J i) : ZMod p) := by
          unfold LightSignedRowHash.lifted
          rw [Int.add_comm (p : ℤ)]
          rw [signed_lift_cast _ (by simpa [Int.add_comm] using hzNonneg i.val i.isLt),hz i]
        rw [hlift,mul_comm]
      _ = _ := physical_dot_eq_logical J (fun i => (raw i : ZMod p))
        (TernaryOriginalRowMenu.seedRow (J+2) (constantCoefficient hf hd) (x,y))
  have hh := congrArg ZMod.val he
  simpa using hh
end ThreeSum.TernaryExtensionEncoding

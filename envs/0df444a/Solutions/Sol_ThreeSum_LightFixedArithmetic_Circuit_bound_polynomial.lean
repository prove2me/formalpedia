-- Prove2me | solution 1 for ThreeSum.LightFixedArithmetic.Circuit.bound_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:48:42.583444+00:00
-- url     : https://prove2.me/submissions/fb6e8a31-6014-4931-bdb5-87285d1d7003

import Definitions.Def_Submission_ThreeSum_LightSignedFiniteTable
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_LightFixedArithmetic
import Theorems.Thm_ThreeSum_LightFixedArithmetic_Circuit_bound_pos
import Theorems.Thm_ThreeSum_LightFixedArithmetic_Circuit_coefficient_pos
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
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
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero



set_option autoImplicit false
open ThreeSum ThreeSum.LightFixedArithmetic
open Light
namespace ThreeSum.LightFixedArithmetic
namespace Circuit
theorem _root_.solution (e : Circuit) {U : ℤ} (hU : 0≤U) :
    e.bound U≤e.coefficient*(U+1)^e.degree := by
  have hbase : 1≤U+1 := by omega
  induction e with
  | literal z => simp [bound,coefficient,degree]
  | atom i => simp [bound,coefficient,degree]
  | add a b ha hb | sub a b ha hb =>
    have hca := a.coefficient_pos
    have hcb := b.coefficient_pos
    have hpa : (U+1)^a.degree≤(U+1)^max a.degree b.degree :=
      pow_le_pow_right₀ hbase (Nat.le_max_left _ _)
    have hpb : (U+1)^b.degree≤(U+1)^max a.degree b.degree :=
      pow_le_pow_right₀ hbase (Nat.le_max_right _ _)
    simp only [bound,coefficient,degree]
    calc
      a.bound U+b.bound U≤a.coefficient*(U+1)^max a.degree b.degree+
          b.coefficient*(U+1)^max a.degree b.degree :=
        add_le_add (ha.trans (mul_le_mul_of_nonneg_left hpa (by omega)))
          (hb.trans (mul_le_mul_of_nonneg_left hpb (by omega)))
      _ = _ := by ring
  | mul a b ha hb =>
    have hpa := a.bound_pos hU
    have hpb := b.bound_pos hU
    simp only [bound,coefficient,degree,pow_add]
    calc
      a.bound U*b.bound U≤(a.coefficient*(U+1)^a.degree)*
          (b.coefficient*(U+1)^b.degree) := mul_le_mul ha hb (by omega) (by nlinarith)
      _ = _ := by ring
end Circuit
end ThreeSum.LightFixedArithmetic

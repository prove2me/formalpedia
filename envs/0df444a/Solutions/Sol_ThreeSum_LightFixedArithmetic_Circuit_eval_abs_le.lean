-- Prove2me | solution 1 for ThreeSum.LightFixedArithmetic.Circuit.eval_abs_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:00:52.055855+00:00
-- url     : https://prove2.me/submissions/869f0c64-a1b5-4e0f-a779-d54ad834d113

import Definitions.Def_Submission_ThreeSum_LightSignedFiniteTable
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_LightFixedArithmetic
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
theorem _root_.solution (e : Circuit) (x : ℕ → ℤ) {U : ℤ}
    (hU : 0≤U) (hx : ∀ i, |x i|≤U) : |e.eval x|≤e.bound U := by
  induction e with
  | literal z => simp only [eval,bound]; omega
  | atom i => exact (hx i).trans (by simp [bound])
  | add a b ha hb => exact (abs_add_le _ _).trans (add_le_add ha hb)
  | sub a b ha hb => exact (abs_sub _ _).trans (add_le_add ha hb)
  | mul a b ha hb =>
    simp only [eval,bound,abs_mul]
    exact mul_le_mul ha hb (abs_nonneg _) (le_trans (abs_nonneg _) ha)
end Circuit
end ThreeSum.LightFixedArithmetic

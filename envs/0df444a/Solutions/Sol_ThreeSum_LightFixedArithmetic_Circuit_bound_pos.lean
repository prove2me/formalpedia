-- Prove2me | solution 1 for ThreeSum.LightFixedArithmetic.Circuit.bound_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:45:01.641397+00:00
-- url     : https://prove2.me/submissions/117c2395-8cc2-49ea-b69e-36fb92fce418

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
theorem _root_.solution (e : Circuit) {U : ℤ} (hU : 0≤U) : 1≤e.bound U := by
  induction e with
  | literal z => simp only [bound]; have := abs_nonneg z; omega
  | atom i => simp only [bound]; omega
  | add a b ha hb => simp only [bound]; omega
  | sub a b ha hb => simp only [bound]; omega
  | mul a b ha hb => simp only [bound]; nlinarith
end Circuit
end ThreeSum.LightFixedArithmetic

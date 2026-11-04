-- Prove2me | solution 1 for ThreeSum.LightFixedArithmetic.Circuit.coefficient_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:41:09.332194+00:00
-- url     : https://prove2.me/submissions/23b3dc4e-b9da-4f7f-a971-eb2dda0618b6

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
theorem _root_.solution (e : Circuit) : 1≤e.coefficient := by
  induction e with
  | literal z => simp only [coefficient]; have := abs_nonneg z; omega
  | atom i => simp [coefficient]
  | add a b ha hb => simp only [coefficient]; omega
  | sub a b ha hb => simp only [coefficient]; omega
  | mul a b ha hb => simp only [coefficient]; nlinarith
end Circuit
end ThreeSum.LightFixedArithmetic

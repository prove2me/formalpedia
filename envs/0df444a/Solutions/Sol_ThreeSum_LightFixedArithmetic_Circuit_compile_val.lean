-- Prove2me | solution 1 for ThreeSum.LightFixedArithmetic.Circuit.compile_val
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:45:03.17686+00:00
-- url     : https://prove2.me/submissions/2856bd22-4bf7-4fb6-859b-fba13632e916

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
theorem _root_.solution (e : Circuit) (atoms : ℕ → Expr) (σ : State) :
    (e.compile atoms).val σ=e.eval (fun i => (atoms i).val σ) := by
  induction e with
  | literal z => simp [compile,LightSignedFiniteTable.literal,Expr.val,Op.eval,eval,Int.toNat_sub_toNat_neg]
  | atom i => rfl
  | add a b ha hb => simp [compile,Expr.val,Op.eval,eval,ha,hb]
  | sub a b ha hb => simp [compile,Expr.val,Op.eval,eval,ha,hb]
  | mul a b ha hb => simp [compile,Expr.val,Op.eval,eval,ha,hb]
end Circuit
end ThreeSum.LightFixedArithmetic

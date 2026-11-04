-- Prove2me | solution 1 for ThreeSum.LightFixedArithmetic.Circuit.compile_safe
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:03:59.878174+00:00
-- url     : https://prove2.me/submissions/cd54e27e-c45b-436f-86cc-4832a7f358c1

import Definitions.Def_Submission_ThreeSum_LightSignedFiniteTable
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_LightFixedArithmetic
import Theorems.Thm_ThreeSum_LightFixedArithmetic_Circuit_bound_pos
import Theorems.Thm_ThreeSum_LightFixedArithmetic_Circuit_eval_abs_le
import Theorems.Thm_ThreeSum_LightFixedArithmetic_Circuit_compile_val
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
theorem _root_.solution (e : Circuit) (atoms : ℕ → Expr) (σ : State)
    {lim : Limits} {U : ℤ} (hU : 0≤U)
    (hs : ∀ i, (atoms i).Safe lim σ)
    (hx : ∀ i, |(atoms i).val σ|≤U) (hw : e.bound U≤lim.word) :
    (e.compile atoms).Safe lim σ := by
  induction e with
  | literal z =>
    have hz := abs_nonneg z
    have hpos := le_abs_self z
    have hneg := neg_le_abs z
    simp only [compile,LightSignedFiniteTable.literal,Expr.Safe,Expr.val,Op.eval]
    refine ⟨?_,?_,?_⟩
    · simp only [bound] at hw; omega
    · simp only [bound] at hw; omega
    · rw [Int.toNat_sub_toNat_neg]; simp only [bound] at hw; omega
  | atom i => exact hs i
  | add a b ha hb =>
    have hpa := a.bound_pos hU
    have hpb := b.bound_pos hU
    refine ⟨ha (by simp only [bound] at hw; omega),hb (by simp only [bound] at hw; omega),?_⟩
    change |(a.compile atoms).val σ+(b.compile atoms).val σ|≤lim.word
    rw [a.compile_val,b.compile_val]
    exact (Circuit.eval_abs_le (.add a b) _ hU hx).trans hw
  | sub a b ha hb =>
    have hpa := a.bound_pos hU
    have hpb := b.bound_pos hU
    refine ⟨ha (by simp only [bound] at hw; omega),hb (by simp only [bound] at hw; omega),?_⟩
    change |(a.compile atoms).val σ-(b.compile atoms).val σ|≤lim.word
    rw [a.compile_val,b.compile_val]
    exact (Circuit.eval_abs_le (.sub a b) _ hU hx).trans hw
  | mul a b ha hb =>
    have hpa := a.bound_pos hU
    have hpb := b.bound_pos hU
    refine ⟨ha (by simp only [bound] at hw; nlinarith),hb (by simp only [bound] at hw; nlinarith),?_⟩
    change |(a.compile atoms).val σ*(b.compile atoms).val σ|≤lim.word
    rw [a.compile_val,b.compile_val]
    exact (Circuit.eval_abs_le (.mul a b) _ hU hx).trans hw
end Circuit
end ThreeSum.LightFixedArithmetic

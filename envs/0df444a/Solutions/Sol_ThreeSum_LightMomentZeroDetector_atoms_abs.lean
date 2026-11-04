-- Prove2me | solution 1 for ThreeSum.LightMomentZeroDetector.atoms_abs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:42:58.459201+00:00
-- url     : https://prove2.me/submissions/982023d6-68ad-4dec-8069-a74efa920196

import Definitions.Def_Submission_ThreeSum_LightMomentDeterminant
import Definitions.Def_Submission_ThreeSum_LightMomentZeroDetector
import Theorems.Thm_ThreeSum_LightMomentZeroDetector_atoms_target
import Theorems.Thm_ThreeSum_LightMomentZeroDetector_atoms_moment
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_LightMomentDeterminant_eval_prodCircuits
import Theorems.Thm_ThreeSum_LightMomentDeterminant_eval_sumCircuits
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
attribute [local simp] ThreeSum.LightMomentDeterminant.eval_prodCircuits
attribute [local simp] ThreeSum.LightMomentDeterminant.eval_sumCircuits
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero


attribute [local simp] ThreeSum.LightMomentZeroDetector.atoms_target

set_option autoImplicit false
open ThreeSum ThreeSum.LightMomentZeroDetector
open Light ThreeSum.LightMomentDeterminant ThreeSum.LightFixedArithmetic
open FiniteMomentZeroDetector
namespace ThreeSum.LightMomentZeroDetector
theorem _root_.solution (H base : ℕ) (a : ℤ) (μ : ℕ → ℤ) (U : ℤ)
    (hU : 0≤U) (ha : |a|≤U) (hm : ∀ k≤2*H, |μ (base+k)|≤U) :
    ∀ i, |(atoms H i).val ⟨frame [base,a],μ⟩|≤U := by
  intro i
  cases i with
  | zero => exact ha
  | succ k =>
    by_cases hk : k≤2*H
    · rw [atoms_moment H base k a μ hk]
      exact hm k hk
    · simpa [atoms,hk,Expr.val] using hU
end ThreeSum.LightMomentZeroDetector

-- Prove2me | solution 1 for ThreeSum.LightMomentZeroDetector.atoms_safe
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:42:18.433227+00:00
-- url     : https://prove2.me/submissions/8cfab3fe-045b-4e57-add0-f7337ee55428

import Definitions.Def_Submission_ThreeSum_LightMomentDeterminant
import Definitions.Def_Submission_ThreeSum_LightMomentZeroDetector
import Theorems.Thm_ThreeSum_LightMomentZeroDetector_atoms_target
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
theorem _root_.solution (H base : ℕ) (a : ℤ) (μ : ℕ → ℤ) {lim : Limits} (hspace : base + (2 * H + 1) ≤ lim.space)
    (hw : (lim.space : ℤ) ≤ lim.word) : ∀ i, (atoms H i).Safe lim ⟨frame [base, a], μ⟩ :=
  by
  intro i
  cases i with
  | zero => trivial
  | succ k =>
    simp only [atoms]
    split_ifs with hk
    · have haddr : base + k < lim.space := by omega
      have haddrWord : ((base + k : ℕ) : ℤ) ≤ lim.word :=
        by
        have hle : ((base + k : ℕ) : ℤ) ≤ (lim.space : ℤ) := by exact_mod_cast (Nat.le_of_lt haddr)
        exact hle.trans hw
      have hkWord : (k : ℤ) ≤ lim.word := by omega
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, haddr, haddrWord, hkWord] <;> omega)
    · change (0 : ℤ) ≤ lim.word
      omega
end ThreeSum.LightMomentZeroDetector

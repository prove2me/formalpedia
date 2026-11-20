-- Prove2me | solution 1 for Sensitivity.BoolFun.restrictTo_sensitivity_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T18:59:07.565684+00:00
-- url     : https://prove2.me/submissions/dc291786-fc1c-40b2-bab0-f1953a59ec61

import Definitions.Def_Sensitivity_Defs
import Definitions.Def_Sensitivity_Multilinear
import Definitions.Def_Sensitivity_Subcube
import Theorems.Thm_Sensitivity_embed_flipBit_free
import Theorems.Thm_Sensitivity_BoolFun_restrictTo_not_sensitiveAt_nonfree
import Theorems.Thm_Sensitivity_BoolFun_localSensitivity_le_sensitivity
import Theorems.Thm_Sensitivity_boolToInt_false
import Theorems.Thm_Sensitivity_boolToInt_true
import Theorems.Thm_Sensitivity_flipBit_apply_ne
import Theorems.Thm_Sensitivity_flipBit_apply_same
import Theorems.Thm_Sensitivity_flipBit_flipBit_same
import Theorems.Thm_Sensitivity_indicator_mem
import Theorems.Thm_Sensitivity_indicator_not_mem
attribute [local simp] Sensitivity.boolToInt_false
attribute [local simp] Sensitivity.boolToInt_true
attribute [local simp] Sensitivity.flipBit_apply_ne
attribute [local simp] Sensitivity.flipBit_apply_same
attribute [local simp] Sensitivity.flipBit_flipBit_same
attribute [local simp] Sensitivity.indicator_mem
attribute [local simp] Sensitivity.indicator_not_mem



set_option autoImplicit false
open Sensitivity
variable {n : ℕ}
namespace Sensitivity
namespace BoolFun
theorem _root_.solution (f : BoolFun n) (free : Finset (Fin n))
    (base : Fin n → Bool) :
    (f.restrictTo free base).sensitivity ≤ f.sensitivity := by
  apply Finset.sup_le
  intro x _
  apply le_trans _ (f.localSensitivity_le_sensitivity (embed free base x))
  unfold localSensitivity
  apply Finset.card_le_card
  intro i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  intro hi
  unfold sensitiveAt at hi ⊢
  by_cases him : i ∈ free
  · unfold restrictTo at hi
    rw [embed_flipBit_free free base x i him] at hi
    exact hi
  · exfalso
    exact f.restrictTo_not_sensitiveAt_nonfree free base x i him hi
end BoolFun
end Sensitivity

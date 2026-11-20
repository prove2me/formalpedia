-- Prove2me | solution 1 for Sensitivity.embed_flipBit_free
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T18:57:22.354878+00:00
-- url     : https://prove2.me/submissions/c577c0e8-83d1-40e9-ba64-5bed514714aa

import Definitions.Def_Sensitivity_Defs
import Definitions.Def_Sensitivity_Multilinear
import Definitions.Def_Sensitivity_Subcube
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
theorem _root_.solution (free : Finset (Fin n)) (base x : Fin n → Bool)
    (i : Fin n) (hi : i ∈ free) :
    embed free base (flipBit x i) = flipBit (embed free base x) i := by
  funext j
  by_cases hji : j = i
  · subst hji; simp [embed, flipBit, hi]
  · by_cases hj : j ∈ free
    · simp [embed, hj, flipBit, Function.update_of_ne hji]
    · simp only [embed, hj, ↓reduceIte, flipBit]
      rw [Function.update_of_ne hji]
      simp [embed, hj]
end Sensitivity

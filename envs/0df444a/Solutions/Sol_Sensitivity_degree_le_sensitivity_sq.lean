-- Prove2me | solution 1 for Sensitivity.degree_le_sensitivity_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T02:58:46.618576+00:00
-- url     : https://prove2.me/submissions/78810783-8698-4bce-9277-fc053c999b12

import Definitions.Def_Sensitivity_Defs
import Definitions.Def_Sensitivity_Basic
import Definitions.Def_Sensitivity_Multilinear
import Definitions.Def_Sensitivity_Main
import Definitions.Def_Sensitivity_Consequences
import Theorems.Thm_Sensitivity_boolToInt_false
import Theorems.Thm_Sensitivity_boolToInt_true
import Theorems.Thm_Sensitivity_flipBit_apply_ne
import Theorems.Thm_Sensitivity_flipBit_apply_same
import Theorems.Thm_Sensitivity_flipBit_flipBit_same
import Theorems.Thm_Sensitivity_indicator_mem
import Theorems.Thm_Sensitivity_indicator_not_mem
import Theorems.Thm_Sensitivity_sensitivity_ge_sqrt_degree
attribute [local simp] Sensitivity.boolToInt_false
attribute [local simp] Sensitivity.boolToInt_true
attribute [local simp] Sensitivity.flipBit_apply_ne
attribute [local simp] Sensitivity.flipBit_apply_same
attribute [local simp] Sensitivity.flipBit_flipBit_same
attribute [local simp] Sensitivity.indicator_mem
attribute [local simp] Sensitivity.indicator_not_mem



set_option autoImplicit false
open Sensitivity
namespace Sensitivity
theorem _root_.solution {n : ℕ} (f : BoolFun n) :
    f.degree ≤ f.sensitivity ^ 2 := by
  by_cases hd : f.degree = 0
  · simp [hd]
  · have hd' : 1 ≤ f.degree := by omega
    have hsqrt := sensitivity_ge_sqrt_degree f hd'
    -- From √d ≤ s (as reals), squaring both sides: d ≤ s²
    -- Since d and s are naturals, this gives the result.
    -- From √d ≤ s we get d ≤ s²
    have hsq : (f.degree : ℝ) ≤ (f.sensitivity : ℝ) ^ 2 := by
      nlinarith [Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) f.degree),
                 Real.sqrt_nonneg (↑f.degree : ℝ)]
    exact_mod_cast hsq
end Sensitivity

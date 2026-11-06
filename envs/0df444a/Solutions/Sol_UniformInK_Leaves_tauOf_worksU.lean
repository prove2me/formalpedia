-- Prove2me | solution 1 for UniformInK.Leaves.tauOf_worksU
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:46:05.626998+00:00
-- url     : https://prove2.me/submissions/879e20d2-87ef-4cfc-aac1-4cfc3408e33f

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_UniformInK_Top_Defs
import Definitions.Def_PaddedDescent_Choice
import Definitions.Def_SparsifyWidthK_Thresholds
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_UniformInK_Top_Leaves
import Theorems.Thm_UniformInK_Leaves_sq_le_of_s0U_le
import Theorems.Thm_UniformInK_Leaves_bsumU_tauOf
import Theorems.Thm_UniformInK_Leaves_three_mul_le
import Theorems.Thm_UniformInK_Leaves_mul_exponent_le
import Theorems.Thm_PaddedDescent_two_le_tauOf


set_option autoImplicit false
section
open UniformInK UniformInK.Leaves
open PaddedDescent
namespace UniformInK.Leaves
theorem _root_.solution {k s : ℕ} (hk : 1 ≤ k) (hs : s0U k ≤ s) :
    ((k : ℝ) / (tauOf s : ℝ)) * Real.logb 2 (Real.exp 1 * (tauOf s : ℝ) * (bsumU (tauOf s) k : ℝ)) ≤ 1 / 2 ^ s := by
  have hτ0 : (0 : ℝ) < (tauOf s : ℝ) := by exact_mod_cast lt_of_lt_of_le (by norm_num) (two_le_tauOf s)
  have hb0 : (0 : ℝ) < (bsumU (tauOf s) k : ℝ) := by
    rw [bsumU_tauOf]
    exact_mod_cast Nat.two_pow_pos _
  have he : Real.exp 1 ≤ 3 := Real.exp_one_lt_three.le
  have h3 : (3 : ℝ) * (tauOf s : ℝ) * (bsumU (tauOf s) k : ℝ) ≤ (2 : ℝ) ^ (betaU k s + 4 * s + 19) := by
    exact_mod_cast three_mul_le k s
  have hle : Real.exp 1 * (tauOf s : ℝ) * (bsumU (tauOf s) k : ℝ) ≤ (2 : ℝ) ^ (betaU k s + 4 * s + 19) :=
    le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right he hτ0.le) hb0.le) h3
  have hlogb : Real.logb 2 (Real.exp 1 * (tauOf s : ℝ) * (bsumU (tauOf s) k : ℝ)) ≤ ((betaU k s + 4 * s + 19 : ℕ) : ℝ) := by
    have hpos : 0 < Real.exp 1 * (tauOf s : ℝ) * (bsumU (tauOf s) k : ℝ) := mul_pos (mul_pos (Real.exp_pos 1) hτ0) hb0
    calc Real.logb 2 (Real.exp 1 * (tauOf s : ℝ) * (bsumU (tauOf s) k : ℝ)) ≤ Real.logb 2 ((2 : ℝ) ^ (betaU k s + 4 * s + 19)) :=
          Real.logb_le_logb_of_le one_lt_two hpos hle
      _ = ((betaU k s + 4 * s + 19 : ℕ) : ℝ) := by rw [Real.logb_pow, Real.logb_self_eq_one one_lt_two, mul_one]
  have h2s : (0 : ℝ) < (2 : ℝ) ^ s := by positivity
  have hnat : k * (betaU k s + 4 * s + 19) * 2 ^ s ≤ 1 * tauOf s := by
    rw [one_mul]
    exact mul_exponent_le hk (sq_le_of_s0U_le hs)
  calc ((k : ℝ) / (tauOf s : ℝ)) * Real.logb 2 (Real.exp 1 * (tauOf s : ℝ) * (bsumU (tauOf s) k : ℝ))
      ≤ ((k : ℝ) / (tauOf s : ℝ)) * ((betaU k s + 4 * s + 19 : ℕ) : ℝ) := mul_le_mul_of_nonneg_left hlogb (div_nonneg (Nat.cast_nonneg k) hτ0.le)
    _ ≤ 1 / 2 ^ s := by
        rw [div_mul_eq_mul_div, div_le_div_iff₀ hτ0 h2s]
        exact_mod_cast hnat
end UniformInK.Leaves

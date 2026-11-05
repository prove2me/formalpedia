-- Prove2me | solution 1 for PaddedDescent.tauOf_works
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T21:55:49.703477+00:00
-- url     : https://prove2.me/submissions/22f8be99-063d-450c-852b-05fe4c24aab1

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_Seq
import Definitions.Def_SparsifyWidthK_Thresholds
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Definitions.Def_PaddedDescent_Choice
import Theorems.Thm_PaddedDescent_two_le_tauOf
import Theorems.Thm_PaddedDescent_le_of_s0K_le
import Theorems.Thm_PaddedDescent_three_mul_tauOf_mul_bsum_le
import Theorems.Thm_PaddedDescent_betaOf_le
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_WidthK_Thresholds_two_le_bsum


set_option autoImplicit false
section
section
set_option exponentiation.threshold 1024
open PaddedDescent
open WidthK (theta bsum leafC)
open WidthK.Thresholds
namespace PaddedDescent
theorem _root_.solution {k s : ℕ} (hs : s0K k ≤ s) :
    ((k : ℝ) / (tauOf s : ℝ)) * Real.logb 2 (Real.exp 1 * (tauOf s : ℝ) * (bsum (tauOf s) k : ℝ)) ≤ 1 / 2 ^ s := by
  have hτ0 : (0 : ℝ) < (tauOf s : ℝ) := by exact_mod_cast lt_of_lt_of_le (by norm_num) (two_le_tauOf s)
  have hb0 : (0 : ℝ) < (bsum (tauOf s) k : ℝ) := by exact_mod_cast lt_of_lt_of_le (by norm_num) (two_le_bsum (tauOf s) k)
  have he : Real.exp 1 ≤ 3 := Real.exp_one_lt_three.le
  have h3 : (3 : ℝ) * (tauOf s : ℝ) * (bsum (tauOf s) k : ℝ) ≤ (2 : ℝ) ^ betaOf s := by
    exact_mod_cast three_mul_tauOf_mul_bsum_le hs
  have hle : Real.exp 1 * (tauOf s : ℝ) * (bsum (tauOf s) k : ℝ) ≤ (2 : ℝ) ^ betaOf s :=
    le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right he hτ0.le) hb0.le) h3
  have hlogb : Real.logb 2 (Real.exp 1 * (tauOf s : ℝ) * (bsum (tauOf s) k : ℝ)) ≤ (betaOf s : ℝ) := by
    have hpos : 0 < Real.exp 1 * (tauOf s : ℝ) * (bsum (tauOf s) k : ℝ) := mul_pos (mul_pos (Real.exp_pos 1) hτ0) hb0
    calc Real.logb 2 (Real.exp 1 * (tauOf s : ℝ) * (bsum (tauOf s) k : ℝ)) ≤ Real.logb 2 ((2 : ℝ) ^ betaOf s) :=
          Real.logb_le_logb_of_le one_lt_two hpos hle
      _ = (betaOf s : ℝ) := by rw [Real.logb_pow, Real.logb_self_eq_one one_lt_two, mul_one]
  have h2s : (0 : ℝ) < (2 : ℝ) ^ s := by positivity
  have hnat : k * betaOf s * 2 ^ s ≤ 1 * tauOf s := by
    have hk : k ≤ 2 ^ s := (le_of_s0K_le hs).trans Nat.lt_two_pow_self.le
    calc k * betaOf s * 2 ^ s ≤ 2 ^ s * (49 * 2 ^ (2 * s)) * 2 ^ s := Nat.mul_le_mul_right _ (Nat.mul_le_mul hk (betaOf_le s))
      _ = 49 * 2 ^ (4 * s) := by rw [show 4 * s = s + 2 * s + s by ring, pow_add, pow_add]; ring
      _ ≤ 2 ^ 17 * 2 ^ (4 * s) := Nat.mul_le_mul_right _ (by norm_num)
      _ = 1 * tauOf s := by rw [tauOf, pow_add]; ring
  calc ((k : ℝ) / (tauOf s : ℝ)) * Real.logb 2 (Real.exp 1 * (tauOf s : ℝ) * (bsum (tauOf s) k : ℝ))
      ≤ ((k : ℝ) / (tauOf s : ℝ)) * (betaOf s : ℝ) := mul_le_mul_of_nonneg_left hlogb (div_nonneg (Nat.cast_nonneg k) hτ0.le)
    _ ≤ 1 / 2 ^ s := by
        rw [div_mul_eq_mul_div, div_le_div_iff₀ hτ0 h2s]
        exact_mod_cast hnat
end PaddedDescent

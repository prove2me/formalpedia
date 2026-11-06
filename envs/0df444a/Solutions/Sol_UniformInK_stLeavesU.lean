-- Prove2me | solution 1 for UniformInK.stLeavesU
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:52:57.506244+00:00
-- url     : https://prove2.me/submissions/c34c5caa-5031-4152-b7b0-3817791e015d

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
import Theorems.Thm_UniformInK_Leaves_tauOf_worksU
import Theorems.Thm_UniformInK_Leaves_le_bsumU
import Theorems.Thm_PaddedDescent_one_le_tauOf
import Theorems.Thm_WidthK_Thresholds_sum_choose_le_two_rpow


set_option autoImplicit false
section
open UniformInK
open PaddedDescent UniformInK.Leaves
namespace UniformInK
theorem _root_.solution : StLeavesU := by
  intro k n s hk hs
  have h1 := WidthK.Thresholds.sum_choose_le_two_rpow (one_le_tauOf s) (le_bsumU k s) (tauOf_worksU hk hs) n
  have h2 : n < 2 ^ s * (n / 2 ^ s + 1) := Nat.lt_mul_div_succ n (by positivity)
  have h3 : (n : ℝ) ≤ (2 : ℝ) ^ s * ((n / 2 ^ s + 1 : ℕ) : ℝ) := by exact_mod_cast h2.le
  have h4 : (1 : ℝ) / 2 ^ s * (n : ℝ) ≤ ((n / 2 ^ s + 1 : ℕ) : ℝ) := by
    have hp : (0 : ℝ) < (2 : ℝ) ^ s := by positivity
    rw [one_div, inv_mul_le_iff₀ hp]
    exact h3
  have h5 : ((∑ j ∈ Finset.range (k * n / tauOf s + 1), (bsumU (tauOf s) k * n).choose j : ℕ) : ℝ) ≤ ((2 ^ (n / 2 ^ s + 1) : ℕ) : ℝ) := by
    calc ((∑ j ∈ Finset.range (k * n / tauOf s + 1), (bsumU (tauOf s) k * n).choose j : ℕ) : ℝ)
        ≤ (2 : ℝ) ^ (1 / 2 ^ s * (n : ℝ)) := h1
      _ ≤ (2 : ℝ) ^ (((n / 2 ^ s + 1 : ℕ) : ℝ)) := Real.rpow_le_rpow_of_exponent_le (by norm_num) h4
      _ = ((2 ^ (n / 2 ^ s + 1) : ℕ) : ℝ) := by rw [Real.rpow_natCast]; push_cast; ring
  exact_mod_cast h5
end UniformInK

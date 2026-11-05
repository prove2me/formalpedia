-- Prove2me | solution 1 for SparsificationLemma.Cal.div_sqrt_le_cube
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:15:05.080203+00:00
-- url     : https://prove2.me/submissions/25b43ecc-62c9-4a65-be32-d112ef673eb8

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsificationLemma_Cal_Defs
import Definitions.Def_SparsificationLemma_Cal_Real
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_SparsificationLemma_Cal_Alpha
import Theorems.Thm_Groundwork_PolyT_div_pow
attribute [local fun_prop] Groundwork.PolyT.div_pow



set_option autoImplicit false
section
section
open SparsificationLemma SparsificationLemma.Cal
namespace SparsificationLemma.Cal
theorem _root_.solution (k : ℕ) {ε : ℚ} (h0 : 0 < ε) (h1 : ε ≤ 1) :
    363 * (k : ℝ) ^ 3 / ((ε : ℝ) * Real.sqrt (ε : ℝ)) ≤ (8 * (k : ℝ) / (ε : ℝ)) ^ 3 := by
  have h0R : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast h0
  have h1R : (ε : ℝ) ≤ 1 := by exact_mod_cast h1
  have hr0 : 0 < Real.sqrt (ε : ℝ) := Real.sqrt_pos.mpr h0R
  have hre : (ε : ℝ) ≤ Real.sqrt (ε : ℝ) := Real.le_sqrt_of_sq_le (by nlinarith)
  have hk3 : 0 ≤ (k : ℝ) ^ 3 := by positivity
  have h3 : (ε : ℝ) ^ 3 ≤ (ε : ℝ) * Real.sqrt (ε : ℝ) := by
    have : (ε : ℝ) ^ 2 ≤ (ε : ℝ) := by nlinarith
    nlinarith
  rw [div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left h3 hk3, mul_nonneg hk3 (mul_pos h0R hr0).le]
end SparsificationLemma.Cal

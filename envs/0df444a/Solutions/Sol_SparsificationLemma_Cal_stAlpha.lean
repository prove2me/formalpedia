-- Prove2me | solution 1 for SparsificationLemma.Cal.stAlpha
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:22:17.656974+00:00
-- url     : https://prove2.me/submissions/a919991c-1da2-4be8-a51e-9b5fcfdaed1f

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
import Theorems.Thm_SparsificationLemma_Cal_logb_le_clog
import Theorems.Thm_SparsificationLemma_Cal_le_xC
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_SparsificationLemma_Cal_seven_le_logb


set_option autoImplicit false
section
section
open SparsificationLemma SparsificationLemma.Cal
namespace SparsificationLemma.Cal
theorem _root_.solution : StAlpha := by
  intro k ε hk h0 h1
  have hk' : (3 : ℚ) ≤ (k : ℚ) := by exact_mod_cast hk
  have hx := le_xC hk h0 h1
  have hx0 : 0 < xC k ε := by linarith
  have hxR : (128 : ℝ) ≤ ((xC k ε : ℚ) : ℝ) := by exact_mod_cast hx
  have hlog : Real.logb 2 ((xC k ε : ℚ) : ℝ) ≤ (logC k ε : ℝ) := logb_le_clog hx0
  have h7R : (7 : ℝ) ≤ (logC k ε : ℝ) := (seven_le_logb hxR).trans hlog
  have h7 : (7 : ℚ) ≤ (logC k ε : ℚ) := by exact_mod_cast h7R
  have hu : 2 * ((k : ℚ) - 1) ^ 2 / ε * (logC k ε : ℚ) = xC k ε / 16 * (logC k ε : ℚ) := by
    rw [xC]; ring
  have hlo : xC k ε / 16 * (logC k ε : ℚ) ≤ (alphaC k ε : ℚ) := by
    rw [← hu]; exact Nat.le_ceil _
  have hhi : (alphaC k ε : ℚ) < xC k ε / 16 * (logC k ε : ℚ) + 1 := by
    rw [← hu]; exact Nat.ceil_lt_add_one (by positivity)
  have hxk : 32 * ((k : ℚ) - 1) ^ 2 ≤ xC k ε := by
    rw [xC, le_div_iff₀ h0]
    have : 0 ≤ ((k : ℚ) - 1) ^ 2 := by positivity
    nlinarith
  have hprod : 7 * xC k ε ≤ xC k ε * (logC k ε : ℚ) := by nlinarith
  have hk2 : ((k ^ 2 : ℕ) : ℚ) ≤ (alphaC k ε : ℚ) := by push_cast; nlinarith
  refine ⟨hx, ?_, by exact_mod_cast hk2, ?_, by linarith⟩
  · have : (2 : ℚ) ≤ (alphaC k ε : ℚ) := by linarith
    exact_mod_cast this
  · have hloR : ((xC k ε : ℚ) : ℝ) / 16 * (logC k ε : ℝ) ≤ (alphaC k ε : ℝ) := by exact_mod_cast hlo
    have : ((xC k ε : ℚ) : ℝ) * Real.logb 2 ((xC k ε : ℚ) : ℝ) ≤ ((xC k ε : ℚ) : ℝ) * (logC k ε : ℝ) :=
      mul_le_mul_of_nonneg_left hlog (by linarith)
    linarith
end SparsificationLemma.Cal

-- Prove2me | solution 1 for SparsificationLemma.Cal.sqrt_xC_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:14:57.439663+00:00
-- url     : https://prove2.me/submissions/16d3adb5-a215-430f-b616-2821f69fdee0

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
import Theorems.Thm_SparsificationLemma_Cal_xC_cast
import Theorems.Thm_Groundwork_PolyT_div_pow
import Theorems.Thm_Groundwork_TM_Run_trans
attribute [local fun_prop] Groundwork.PolyT.div_pow



set_option autoImplicit false
section
section
open SparsificationLemma SparsificationLemma.Cal
namespace SparsificationLemma.Cal
theorem _root_.solution {k : ℕ} {ε : ℚ} (hk : 3 ≤ k) (h0 : 0 < ε) :
    2 * ((xC k ε : ℚ) : ℝ) * Real.sqrt ((xC k ε : ℚ) : ℝ) ≤ 363 * (k : ℝ) ^ 3 / ((ε : ℝ) * Real.sqrt (ε : ℝ)) := by
  have hkR : (3 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have h0R : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast h0
  have hr0 : 0 < Real.sqrt (ε : ℝ) := Real.sqrt_pos.mpr h0R
  have hr2 : Real.sqrt (ε : ℝ) ^ 2 = (ε : ℝ) := Real.sq_sqrt h0R.le
  rw [xC_cast]
  have hx0 : 0 ≤ 32 * ((k : ℝ) - 1) ^ 2 / (ε : ℝ) := by positivity
  have hw : Real.sqrt (32 * ((k : ℝ) - 1) ^ 2 / (ε : ℝ)) ≤ 5.66 * ((k : ℝ) - 1) / Real.sqrt (ε : ℝ) := by
    rw [Real.sqrt_le_iff]
    refine ⟨div_nonneg (by linarith) hr0.le, ?_⟩
    rw [div_pow, hr2]
    apply div_le_div_of_nonneg_right _ h0R.le
    have : 0 ≤ ((k : ℝ) - 1) ^ 2 := by positivity
    nlinarith
  refine (mul_le_mul_of_nonneg_left hw (by linarith)).trans ?_
  have e1 : 2 * (32 * ((k : ℝ) - 1) ^ 2 / (ε : ℝ)) * (5.66 * ((k : ℝ) - 1) / Real.sqrt (ε : ℝ))
      = 362.24 * ((k : ℝ) - 1) ^ 3 / ((ε : ℝ) * Real.sqrt (ε : ℝ)) := by
    field_simp; ring
  rw [e1]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have c1 : ((k : ℝ) - 1) ^ 3 ≤ (k : ℝ) ^ 3 := pow_le_pow_left₀ (by linarith) (by linarith) 3
  have c2 : 0 ≤ ((k : ℝ) - 1) ^ 3 := pow_nonneg (by linarith) 3
  nlinarith
end SparsificationLemma.Cal

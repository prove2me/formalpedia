-- Prove2me | solution 1 for SparsificationLemma.Cal.mul_logb_div_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:21:58.39197+00:00
-- url     : https://prove2.me/submissions/4d0e4010-f57d-491e-a9ea-1d76449bce7e

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsificationLemma_Cal_Defs
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_SparsificationLemma_Cal_Real
import Theorems.Thm_SparsificationLemma_Cal_seven_le_logb
import Theorems.Thm_SparsificationLemma_Cal_two_logb_le
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
open SparsificationLemma SparsificationLemma.Cal
namespace SparsificationLemma.Cal
theorem _root_.solution {X t ε : ℝ} (hε : 0 < ε) (hX : 128 ≤ X) (ht : 2 * X * Real.logb 2 X ≤ t) :
    ε * X * Real.logb 2 t / t ≤ ε := by
  have hX0 : 0 < X := by linarith
  have hL0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h7 := seven_le_logb hX
  have hl0 : 0 < Real.logb 2 X := by linarith
  have hlX : Real.log X = Real.logb 2 X * Real.log 2 := by rw [Real.logb, div_mul_cancel₀ _ hL0.ne']
  have ht0 : 0 < 2 * X * Real.logb 2 X := by positivity
  have htpos : 0 < t := by linarith
  have he : Real.exp 1 ≤ 2 * X * Real.logb 2 X := by
    have := Real.exp_one_lt_d9
    nlinarith
  have hanti : Real.log t / t ≤ Real.log (2 * X * Real.logb 2 X) / (2 * X * Real.logb 2 X) :=
    Real.log_div_self_antitoneOn he (le_trans he ht) ht
  have hsq : Real.log (2 * X * Real.logb 2 X) ≤ 2 * Real.log X := by
    have h2 := two_logb_le hX
    have : Real.log (2 * X * Real.logb 2 X) ≤ Real.log (X ^ 2) := Real.log_le_log ht0 (by nlinarith)
    rwa [Real.log_pow, Nat.cast_ofNat] at this
  have h1 : Real.log t / t ≤ Real.log 2 / X := by
    refine hanti.trans ?_
    rw [div_le_div_iff₀ ht0 hX0]
    rw [hlX] at hsq
    nlinarith
  have h2 : X * Real.log t ≤ t * Real.log 2 := by
    rw [div_le_div_iff₀ htpos hX0] at h1
    linarith
  have h3 : X * Real.logb 2 t ≤ t := by
    rw [Real.logb, ← mul_div_assoc, div_le_iff₀ hL0]
    exact h2
  rw [div_le_iff₀ htpos]
  nlinarith
end SparsificationLemma.Cal

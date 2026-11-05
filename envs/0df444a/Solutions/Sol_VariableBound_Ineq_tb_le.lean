-- Prove2me | solution 1 for VariableBound.Ineq.tb_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:56:13.744128+00:00
-- url     : https://prove2.me/submissions/f74090a6-a338-478b-9c42-c625805fefd8

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Params_Defs
import Definitions.Def_ClauseBound_ParityChecks_Binom
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_VariableBound_Params_Ineq
import Theorems.Thm_VariableBound_Ineq_two_le_lg
import Theorems.Thm_VariableBound_Ineq_p_rb
import Theorems.Thm_VariableBound_Ineq_lg_one_add_le

set_option autoImplicit false
section
section
open VariableBound
open AppVariables
open VariableBound.Ineq
namespace VariableBound.Ineq
theorem _root_.solution {n Δ m nb rb tb : ℕ} (hΔ : 2 ≤ Δ) (hm : 1 ≤ m) (h : IsNb n Δ nb) (hr : rb ≤ 10 * n) (ht : IsTb m nb rb tb) :
    (tb : ℝ) ≤ lg m + 33 * lg (2 * Δ) + 1 := by
  have hL := two_le_lg hΔ
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hlm : 0 ≤ lg m := Real.logb_nonneg (by norm_num) hm1
  rcases Nat.eq_zero_or_pos tb with rfl | hpos
  · push_cast
    linarith
  · obtain ⟨c, rfl⟩ : ∃ c, tb = c + 1 := ⟨tb - 1, by omega⟩
    have h1 : (2 : ℚ) ^ c < (m : ℚ) * (1 + pp nb) ^ rb := not_le.1 (ht.2 c (Nat.lt_succ_self c))
    have h2 : (2 : ℝ) ^ c < (m : ℝ) * (1 + ((pp nb : ℚ) : ℝ)) ^ rb := by exact_mod_cast h1
    have hp : (0 : ℝ) ≤ ((pp nb : ℚ) : ℝ) := by
      unfold pp
      push_cast
      positivity
    have h3 := Real.logb_lt_logb (b := 2) (by norm_num) (by positivity) h2
    rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one, Real.logb_mul (by linarith) (by positivity), Real.logb_pow] at h3
    have h4 : (rb : ℝ) * Real.logb 2 (1 + ((pp nb : ℚ) : ℝ)) ≤ rb * (3 / 2 * ((pp nb : ℚ) : ℝ)) :=
      mul_le_mul_of_nonneg_left (lg_one_add_le hp) (Nat.cast_nonneg rb)
    have h5 := p_rb hΔ h hr
    have h6 : lg m = Real.logb 2 m := rfl
    push_cast
    linarith
end VariableBound.Ineq

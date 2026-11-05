-- Prove2me | solution 1 for VariableBound.Ineq.p_rb
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:56:15.756045+00:00
-- url     : https://prove2.me/submissions/ebf4ce08-f2bc-4b3e-8393-904b24526770

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
import Theorems.Thm_VariableBound_Ineq_lt_nb_mul
import Theorems.Thm_VariableBound_Ineq_nb_pos

set_option autoImplicit false
section
section
open VariableBound
open AppVariables
open VariableBound.Ineq
namespace VariableBound.Ineq
theorem _root_.solution {n Δ nb rb : ℕ} (hΔ : 2 ≤ Δ) (h : IsNb n Δ nb) (hr : rb ≤ 10 * n) : ((pp nb : ℚ) : ℝ) * rb < 22 * lg (2 * Δ) := by
  have hL := two_le_lg hΔ
  have hnb := nb_pos h
  have h1 := lt_nb_mul h
  have h2 : (rb : ℝ) ≤ 10 * n := by exact_mod_cast hr
  unfold pp
  push_cast
  rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
  nlinarith
end VariableBound.Ineq

-- Prove2me | solution 1 for VariableBound.Ineq.two_le_lg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:49:55.793199+00:00
-- url     : https://prove2.me/submissions/fbe5c294-3eee-442c-b59f-981c87d6be55

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Params_Defs
import Definitions.Def_ClauseBound_ParityChecks_Binom
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_VariableBound_Params_Ineq

set_option autoImplicit false
section
section
open VariableBound
open AppVariables
open VariableBound.Ineq
namespace VariableBound.Ineq
theorem _root_.solution {Δ : ℕ} (hΔ : 2 ≤ Δ) : 2 ≤ lg (2 * Δ) := by
  have h : (2 : ℝ) ^ (2 : ℕ) ≤ 2 * Δ := by
    have : (2 : ℝ) ≤ Δ := by exact_mod_cast hΔ
    linarith
  have h2 := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by positivity) h
  rwa [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one, Nat.cast_ofNat] at h2
end VariableBound.Ineq

-- Prove2me | solution 1 for VariableBound.Ineq.lg_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:55:04.311935+00:00
-- url     : https://prove2.me/submissions/3ec6557a-8202-4fa4-8fb9-e7be76abcbc9

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
theorem _root_.solution {Δ : ℕ} (hΔ : 1 ≤ Δ) : lg (2 * Δ) ≤ 2 * Δ := by
  have h : ((2 * Δ : ℕ) : ℝ) ≤ (2 : ℝ) ^ (2 * Δ) := by exact_mod_cast (Nat.lt_two_pow_self (n := 2 * Δ)).le
  have h0 : (0 : ℝ) < ((2 * Δ : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < 2 * Δ)
  have h2 := Real.logb_le_logb_of_le (b := 2) (by norm_num) h0 h
  rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one] at h2
  push_cast at h2
  exact h2
end VariableBound.Ineq

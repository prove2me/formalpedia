-- Prove2me | solution 1 for VariableBound.Ineq.nb_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:54:41.155368+00:00
-- url     : https://prove2.me/submissions/c9a1e2ac-35c5-4481-b261-c051162f2c39

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
theorem _root_.solution {n Δ nb : ℕ} (hΔ : 1 ≤ Δ) (h : IsNb n Δ nb) : (nb : ℝ) * lg (2 * Δ) ≤ n := by
  have h1 : ((2 : ℝ) * Δ) ^ nb ≤ 2 ^ n := by exact_mod_cast h.2.1
  have h0 : (0 : ℝ) < 2 * Δ := by
    have : (1 : ℝ) ≤ Δ := by exact_mod_cast hΔ
    linarith
  have h2 := Real.logb_le_logb_of_le (b := 2) (by norm_num) (pow_pos h0 nb) h1
  rwa [Real.logb_pow, Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one] at h2
end VariableBound.Ineq

-- Prove2me | solution 1 for VariableBound.Ineq.six_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:56:19.010082+00:00
-- url     : https://prove2.me/submissions/172e8f08-a21f-4c01-ad8f-b9c1b1c4f037

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Params_Defs
import Definitions.Def_ClauseBound_ParityChecks_Binom
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_VariableBound_Params_Ineq
import Theorems.Thm_VariableBound_Ineq_lg_le

set_option autoImplicit false
section
section
open VariableBound
open AppVariables
open VariableBound.Ineq
namespace VariableBound.Ineq
theorem _root_.solution {Δ : ℕ} (hΔ : 2 ≤ Δ) : 6 * (Δ : ℝ) * lg (2 * Δ) ≤ (2 * Δ) ^ 3 := by
  have h1 := lg_le (Δ := Δ) (by omega)
  have h2 : (2 : ℝ) ≤ Δ := by exact_mod_cast hΔ
  have h3 : 6 * (Δ : ℝ) * lg (2 * Δ) ≤ 6 * Δ * (2 * Δ) := mul_le_mul_of_nonneg_left h1 (by linarith)
  nlinarith [mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ Δ) (by linarith : (0 : ℝ) ≤ Δ)) (by linarith : (0 : ℝ) ≤ Δ - 2)]
end VariableBound.Ineq

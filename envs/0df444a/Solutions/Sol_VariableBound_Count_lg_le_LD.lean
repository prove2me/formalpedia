-- Prove2me | solution 1 for VariableBound.Count.lg_le_LD
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T02:32:05.134281+00:00
-- url     : https://prove2.me/submissions/b4297d5a-fa51-416b-9b91-0695ead7112c

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Count_Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_VariableBound_Count_Correct

set_option autoImplicit false
section
section
open VariableBound VariableBound.Count
open Groundwork Groundwork.Prog PaddedDescent.F PaddedDescent.F.Mark ClauseBound.Alg ClauseBound.ParityChecks AppVariables VariableBound.Net Finset
namespace VariableBound.Count
theorem _root_.solution (Δ : ℕ) (hΔ : 1 ≤ Δ) : lg (2 * Δ) ≤ LD Δ := by
  have h1 : (2 * Δ : ℕ) ≤ 2 ^ LD Δ := Nat.le_pow_clog (by norm_num) _
  have h2 : (2 * Δ : ℝ) ≤ 2 ^ LD Δ := by exact_mod_cast h1
  have h3 : (0 : ℝ) < 2 * Δ := by
    have : (0 : ℝ) < Δ := by exact_mod_cast hΔ
    positivity
  unfold lg
  calc Real.logb 2 (2 * Δ) ≤ Real.logb 2 (2 ^ LD Δ) := Real.logb_le_logb_of_le (by norm_num) h3 h2
    _ = LD Δ := by rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one]
end VariableBound.Count

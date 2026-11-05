-- Prove2me | solution 1 for PairsToBound.length_le_rpow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T01:41:47.286741+00:00
-- url     : https://prove2.me/submissions/fe0a1c98-6c26-48fa-8fc6-701f8b0c012c

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PairsToBound_Defs
import Definitions.Def_VariableBound_Paper_Arith
import Definitions.Def_VariableBound_Printed_VariablesA_StepSparsify
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Definitions.Def_PairsToBound_Arith
import Theorems.Thm_PairsToBound_mul_lg_le_expN
import Theorems.Thm_PairsToBound_natCast_pow_eq
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
open PairsToBound
open MainTheoremForms VariableBound.Paper
namespace PairsToBound
theorem _root_.solution {k n len : ℕ} (hk : 1 ≤ k) (hn : 4 ≤ n) (hlen : len + 1 ≤ (n + 2) ^ (5 * k)) : ((len + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (((10 : ℕ) : ℝ) * expN k n) := by
  have h1 : (n + 2) ^ (5 * k) ≤ n ^ (10 * k) := by
    calc (n + 2) ^ (5 * k) ≤ (n ^ 2) ^ (5 * k) := Nat.pow_le_pow_left (by nlinarith) _
      _ = n ^ (10 * k) := by rw [← pow_mul, show 2 * (5 * k) = 10 * k by ring]
  calc ((len + 1 : ℕ) : ℝ) ≤ ((n ^ (10 * k) : ℕ) : ℝ) := by exact_mod_cast hlen.trans h1
    _ = (2 : ℝ) ^ (((10 * k : ℕ) : ℝ) * lg n) := by rw [Nat.cast_pow, natCast_pow_eq (by omega)]
    _ ≤ (2 : ℝ) ^ (((10 : ℕ) : ℝ) * expN k n) := by
        refine Real.rpow_le_rpow_of_exponent_le one_le_two ?_
        have := mul_lg_le_expN hk hn
        push_cast
        nlinarith
end PairsToBound

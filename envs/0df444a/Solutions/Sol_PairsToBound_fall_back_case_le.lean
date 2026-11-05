-- Prove2me | solution 1 for PairsToBound.fall_back_case_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:14:49.761607+00:00
-- url     : https://prove2.me/submissions/c94b0a66-ffea-4090-b3d5-1abeb34806e6

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
import Theorems.Thm_PairsToBound_two_rpow_mono
import Theorems.Thm_PairsToBound_choice_le
import Theorems.Thm_PairsToBound_length_le_rpow
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_VariableBound_Paper_two_le_expN


set_option autoImplicit false
section
section
open PairsToBound
open MainTheoremForms VariableBound.Paper
namespace PairsToBound
theorem _root_.solution (q c D c₁ : ℕ) (h1 : c * (D + 1) ≤ c₁) (h2 : 10 ≤ c₁) {k n len : ℕ} (hk : 1 ≤ k) (hn : 4 ≤ n) (hD : (n : ℝ) ≤ (D : ℝ) * expN k n) (hlen : len + 1 ≤ (n + 2) ^ (5 * k)) :
    q * (2 ^ (c * n) * n ^ (c * k) + len + 1) ^ q ≤ timeN (q * (c₁ + 2)) k n := by
  have hX := two_le_expN hk hn
  refine choice_le q c₁ (by linarith) ?_ ((length_le_rpow hk hn hlen).trans (two_rpow_mono h2 (by linarith)))
  calc ((2 ^ (c * n) * n ^ (c * k) : ℕ) : ℝ) = (2 : ℝ) ^ (((c * n : ℕ) : ℝ) + ((c * k : ℕ) : ℝ) * lg n) := by
        rw [Real.rpow_add two_pos, Real.rpow_natCast, ← natCast_pow_eq (by omega)]
        push_cast
        ring
    _ ≤ (2 : ℝ) ^ (((c * (D + 1) : ℕ) : ℝ) * expN k n) := by
        refine Real.rpow_le_rpow_of_exponent_le one_le_two ?_
        have a1 := mul_le_mul_of_nonneg_left hD (Nat.cast_nonneg c : (0 : ℝ) ≤ c)
        have a2 := mul_le_mul_of_nonneg_left (mul_lg_le_expN hk hn) (Nat.cast_nonneg c : (0 : ℝ) ≤ c)
        push_cast
        linarith
    _ ≤ _ := two_rpow_mono h1 (by linarith)
end PairsToBound

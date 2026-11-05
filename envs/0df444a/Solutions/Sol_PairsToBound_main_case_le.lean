-- Prove2me | solution 1 for PairsToBound.main_case_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:14:48.776168+00:00
-- url     : https://prove2.me/submissions/a462e312-7f94-4bc5-839d-617c3140d576

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
import Theorems.Thm_PairsToBound_expN_le_nine
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
theorem _root_.solution (q C₁ c₁ : ℕ) (h1 : 9 * C₁ ≤ c₁) (h2 : 10 ≤ c₁) {k k' n len : ℕ} (hk : 1 ≤ k) (hn : 4 ≤ n) (hkk : k' ^ 2 ≤ 9 * k ^ 2) (hlen : len + 1 ≤ (n + 2) ^ (5 * k)) :
    q * (timeN C₁ k' n + len + 1) ^ q ≤ timeN (q * (c₁ + 2)) k n := by
  have hX := two_le_expN hk hn
  refine choice_le q c₁ (by linarith) ?_ ((length_le_rpow hk hn hlen).trans (two_rpow_mono h2 (by linarith)))
  calc (timeN C₁ k' n : ℝ) ≤ (2 : ℝ) ^ ((C₁ : ℝ) * expN k' n) := Nat.floor_le (by positivity)
    _ ≤ (2 : ℝ) ^ (((9 * C₁ : ℕ) : ℝ) * expN k n) := by
        refine Real.rpow_le_rpow_of_exponent_le one_le_two ?_
        have := mul_le_mul_of_nonneg_left (expN_le_nine hn hkk) (Nat.cast_nonneg C₁ : (0 : ℝ) ≤ C₁)
        push_cast
        linarith
    _ ≤ _ := two_rpow_mono h1 (by linarith)
end PairsToBound

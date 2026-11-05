-- Prove2me | solution 1 for PairsToBound.lg_cube_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T01:29:27.569659+00:00
-- url     : https://prove2.me/submissions/b9af136c-52a0-48ad-bbee-0f0323b8574b

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

set_option autoImplicit false
section
section
open PairsToBound
open MainTheoremForms VariableBound.Paper
namespace PairsToBound
theorem _root_.solution {n : ℕ} (hn : 1 ≤ n) : lg n ^ 3 ≤ (n : ℝ) ^ 2 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hl2 : 0.69 < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hlog : lg n * Real.log 2 = Real.log n := by
    unfold lg
    rw [Real.logb, div_mul_cancel₀ _ (by linarith : Real.log 2 ≠ 0)]
  have hL0 : 0 ≤ lg n := Real.logb_nonneg one_lt_two hn1
  obtain ⟨y, hy⟩ : ∃ y, y = 2 / 3 * Real.log n := ⟨_, rfl⟩
  have hy0 : 0 ≤ y := by rw [hy]; have := Real.log_nonneg hn1; positivity
  have h1 := Real.quadratic_le_exp_of_nonneg hy0
  have h2 : lg n ≤ Real.exp y := by
    have h3 : 0.69 * lg n ≤ 3 / 2 * y := by rw [hy]; nlinarith
    nlinarith [sq_nonneg (y - 27 / 23)]
  calc lg n ^ 3 ≤ Real.exp y ^ 3 := pow_le_pow_left₀ hL0 h2 3
    _ = (n : ℝ) ^ 2 := by
      rw [← Real.exp_nat_mul, show ((3 : ℕ) : ℝ) * y = ((2 : ℕ) : ℝ) * Real.log n by rw [hy]; push_cast; ring, Real.exp_nat_mul, Real.exp_log hn0]
end PairsToBound

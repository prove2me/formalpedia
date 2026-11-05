-- Prove2me | solution 1 for PairsToBound.expVariablesA_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T01:28:47.152076+00:00
-- url     : https://prove2.me/submissions/7208c859-ce93-47f9-8e41-8f4c0fdafb11

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
import Theorems.Thm_VariableBound_Paper_lg_mono


set_option autoImplicit false
section
section
open PairsToBound
open MainTheoremForms VariableBound.Paper
namespace PairsToBound
theorem _root_.solution {k k' n : ℕ} {e : ℝ} (hk : 3 ≤ k) (h : k ≤ k') (he : 0 < e) (he1 : e ≤ 1) : expVariablesA k n e ≤ expVariablesA k' n e := by
  have hk3 : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hkk : (k : ℝ) ≤ k' := by exact_mod_cast h
  have h1 : 1 ≤ (k : ℝ) / e := by rw [le_div_iff₀ he]; linarith
  have hl0 : 0 ≤ lg ((k : ℝ) / e) := Real.logb_nonneg one_lt_two h1
  have hl : lg ((k : ℝ) / e) ≤ lg ((k' : ℝ) / e) := lg_mono (by linarith) (div_le_div_of_nonneg_right hkk he.le)
  unfold expVariablesA
  exact mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg k) hkk 2) he.le) (Nat.cast_nonneg n)) hl hl0 (by positivity)
end PairsToBound

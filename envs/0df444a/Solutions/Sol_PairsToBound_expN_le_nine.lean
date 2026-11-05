-- Prove2me | solution 1 for PairsToBound.expN_le_nine
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T01:29:43.656592+00:00
-- url     : https://prove2.me/submissions/dd84eedd-7ed4-4521-95af-10afdb10f059

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
import Theorems.Thm_VariableBound_Paper_expN_eq
import Theorems.Thm_VariableBound_Paper_two_le_base


set_option autoImplicit false
section
section
open PairsToBound
open MainTheoremForms VariableBound.Paper
namespace PairsToBound
theorem _root_.solution {k k' n : ℕ} (hn : 4 ≤ n) (h : k' ^ 2 ≤ 9 * k ^ 2) : expN k' n ≤ 9 * expN k n := by
  have h' : (k' : ℝ) ^ 2 ≤ 9 * (k : ℝ) ^ 2 := by exact_mod_cast h
  rw [expN_eq, expN_eq]
  calc (k' : ℝ) ^ 2 * ((n : ℝ) * lg (lg n) / Real.sqrt (lg n)) ≤ 9 * (k : ℝ) ^ 2 * ((n : ℝ) * lg (lg n) / Real.sqrt (lg n)) :=
        mul_le_mul_of_nonneg_right h' (by linarith [two_le_base hn])
    _ = _ := by ring
end PairsToBound

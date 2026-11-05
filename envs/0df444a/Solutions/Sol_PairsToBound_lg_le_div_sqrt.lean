-- Prove2me | solution 1 for PairsToBound.lg_le_div_sqrt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T01:32:48.405472+00:00
-- url     : https://prove2.me/submissions/dd86e9b6-64a1-4b98-98ba-26bcdc34568d

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
import Theorems.Thm_PairsToBound_lg_cube_le
import Theorems.Thm_VariableBound_Paper_one_le_lg


set_option autoImplicit false
section
section
open PairsToBound
open MainTheoremForms VariableBound.Paper
namespace PairsToBound
theorem _root_.solution {n : ℕ} (hn : 2 ≤ n) : lg n ≤ n / Real.sqrt (lg n) := by
  have hL := one_le_lg hn
  have hs : 0 < Real.sqrt (lg n) := Real.sqrt_pos.2 (by linarith)
  rw [le_div_iff₀ hs]
  refine (sq_le_sq₀ (by positivity) (Nat.cast_nonneg n)).1 ?_
  rw [mul_pow, Real.sq_sqrt (by linarith)]
  calc lg n ^ 2 * lg n = lg n ^ 3 := by ring
    _ ≤ (n : ℝ) ^ 2 := lg_cube_le (by omega)
end PairsToBound

-- Prove2me | solution 1 for PairsToBound.natCast_pow_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T00:00:03.118217+00:00
-- url     : https://prove2.me/submissions/16102863-5661-4ea8-8b25-5161835092ca

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
theorem _root_.solution {n : ℕ} (hn : 1 ≤ n) (j : ℕ) : (n : ℝ) ^ j = (2 : ℝ) ^ ((j : ℝ) * lg n) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [mul_comm, Real.rpow_mul two_pos.le, lg, Real.rpow_logb two_pos (by norm_num) hn0, Real.rpow_natCast]
end PairsToBound

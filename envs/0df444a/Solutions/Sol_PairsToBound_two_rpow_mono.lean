-- Prove2me | solution 1 for PairsToBound.two_rpow_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T00:14:00.172832+00:00
-- url     : https://prove2.me/submissions/7fd2f086-8182-4b48-a0f2-dcb790d19829

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
theorem _root_.solution {a b : ℕ} (h : a ≤ b) {X : ℝ} (hX : 0 ≤ X) : (2 : ℝ) ^ ((a : ℝ) * X) ≤ (2 : ℝ) ^ ((b : ℝ) * X) :=
  Real.rpow_le_rpow_of_exponent_le one_le_two (mul_le_mul_of_nonneg_right (by exact_mod_cast h) hX)
end PairsToBound

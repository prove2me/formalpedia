-- Prove2me | solution 1 for ThmVariables.boundAtANumberBetween
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:25:49.2292+00:00
-- url     : https://prove2.me/submissions/6925d6d6-1d34-463d-8e60-6af83dad8aec

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThmVariables_Defs
import Definitions.Def_RecursionToBound_Numbers
import Definitions.Def_VariableBound_Paper_Arith
import Definitions.Def_VariableBound_Printed_VariablesA_Arith
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Definitions.Def_ThmVariables_Bound
import Theorems.Thm_ThmVariables_expVariablesA_le_two_mul

set_option autoImplicit false
section
section
open ThmVariables
open Turing CliqueLevels MainTheoremForms VariableBound.Paper
open Sat3 (CNF)
variable {K : ℕ → ℕ} {e : ℕ → ℝ} {C₀ : ℕ}
namespace ThmVariables
theorem _root_.solution : BoundAtANumberBetween := by
  intro C k n e e' hk he h1 h2 h3
  unfold timeVariablesA
  refine Nat.floor_le_floor (Real.rpow_le_rpow_of_exponent_le one_le_two ?_)
  have := mul_le_mul_of_nonneg_left (expVariablesA_le_two_mul (n := n) hk he h1 h2 h3) (Nat.cast_nonneg C : (0 : ℝ) ≤ C)
  push_cast
  linarith
end ThmVariables

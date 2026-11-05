-- Prove2me | solution 1 for VariableBound.Paper.natCast_le_two_rpow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:30:26.423821+00:00
-- url     : https://prove2.me/submissions/9ae4a0ef-9a41-4e6a-ae27-5108a897f391

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_MainTheoremFormsStatement
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Definitions.Def_VariableBound_Paper_Arith

set_option autoImplicit false
section
section
open VariableBound VariableBound.Paper
open MainTheoremForms
namespace VariableBound.Paper
theorem _root_.solution (C : ℕ) {X : ℝ} (hX : 1 ≤ X) : (C : ℝ) ≤ (2 : ℝ) ^ ((C : ℝ) * X) := by
  have h1 : (C : ℝ) ≤ (2 : ℝ) ^ (C : ℝ) := by
    rw [Real.rpow_natCast]
    exact_mod_cast Nat.lt_two_pow_self.le
  exact h1.trans (Real.rpow_le_rpow_of_exponent_le one_le_two (le_mul_of_one_le_right (Nat.cast_nonneg C) hX))
end VariableBound.Paper

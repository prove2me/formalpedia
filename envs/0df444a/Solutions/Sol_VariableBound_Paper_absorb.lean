-- Prove2me | solution 1 for VariableBound.Paper.absorb
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:37:28.940353+00:00
-- url     : https://prove2.me/submissions/6d48e6f1-2f76-4953-ad97-f898487d4f9b

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
import Theorems.Thm_VariableBound_Paper_natCast_le_two_rpow

set_option autoImplicit false
section
section
open VariableBound VariableBound.Paper
open MainTheoremForms
namespace VariableBound.Paper
theorem _root_.solution (C : ℕ) {E X : ℝ} (hE : E ≤ 2 * X) (hX : 1 ≤ X) : (C : ℝ) * (2 : ℝ) ^ ((C : ℝ) * E) ≤ (2 : ℝ) ^ (((3 * C : ℕ) : ℝ) * X) := by
  have hC0 : (0 : ℝ) ≤ C := Nat.cast_nonneg C
  calc (C : ℝ) * (2 : ℝ) ^ ((C : ℝ) * E) ≤ (2 : ℝ) ^ ((C : ℝ) * X) * (2 : ℝ) ^ ((C : ℝ) * (2 * X)) :=
        mul_le_mul (natCast_le_two_rpow C hX) (Real.rpow_le_rpow_of_exponent_le one_le_two (mul_le_mul_of_nonneg_left hE hC0)) (by positivity) (by positivity)
    _ = (2 : ℝ) ^ (((3 * C : ℕ) : ℝ) * X) := by
      rw [← Real.rpow_add two_pos]
      congr 1
      push_cast
      ring
end VariableBound.Paper

-- Prove2me | solution 1 for PairsToBound.choice_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T00:14:04.528442+00:00
-- url     : https://prove2.me/submissions/4888a093-1b7e-4ac4-9105-d6fa587771a3

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
import Theorems.Thm_Groundwork_PolyT_congr
import Theorems.Thm_VariableBound_Paper_natCast_le_two_rpow


set_option autoImplicit false
section
section
open PairsToBound
open MainTheoremForms VariableBound.Paper
namespace PairsToBound
theorem _root_.solution (q c₁ : ℕ) {t len : ℕ} {X : ℝ} (hX : 1 ≤ X) (ht : (t : ℝ) ≤ (2 : ℝ) ^ ((c₁ : ℝ) * X)) (hl : ((len + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ ((c₁ : ℝ) * X)) :
    q * (t + len + 1) ^ q ≤ ⌊(2 : ℝ) ^ (((q * (c₁ + 2) : ℕ) : ℝ) * X)⌋₊ := by
  refine Nat.le_floor ?_
  have h1 : (t : ℝ) + len + 1 ≤ (2 : ℝ) ^ (((c₁ : ℝ) + 1) * X) := by
    have e : (2 : ℝ) ^ (((c₁ : ℝ) + 1) * X) = (2 : ℝ) ^ ((c₁ : ℝ) * X) * (2 : ℝ) ^ X := by
      rw [← Real.rpow_add two_pos]
      congr 1
      ring
    have h2 : (2 : ℝ) ≤ (2 : ℝ) ^ X := by
      have := Real.rpow_le_rpow_of_exponent_le one_le_two hX
      rwa [Real.rpow_one] at this
    have hp : (0 : ℝ) < (2 : ℝ) ^ ((c₁ : ℝ) * X) := by positivity
    push_cast at hl
    rw [e]
    nlinarith
  calc ((q * (t + len + 1) ^ q : ℕ) : ℝ) = (q : ℝ) * ((t : ℝ) + len + 1) ^ q := by push_cast; ring
    _ ≤ (2 : ℝ) ^ ((q : ℝ) * X) * ((2 : ℝ) ^ (((c₁ : ℝ) + 1) * X)) ^ q :=
        mul_le_mul (natCast_le_two_rpow q hX) (pow_le_pow_left₀ (by positivity) h1 q) (by positivity) (by positivity)
    _ = (2 : ℝ) ^ (((q * (c₁ + 2) : ℕ) : ℝ) * X) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul two_pos.le, ← Real.rpow_add two_pos]
        congr 1
        push_cast
        ring
end PairsToBound

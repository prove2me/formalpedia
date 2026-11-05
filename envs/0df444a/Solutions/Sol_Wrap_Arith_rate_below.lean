-- Prove2me | solution 1 for Wrap.Arith.rate_below
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:56:21.876086+00:00
-- url     : https://prove2.me/submissions/e74bbf88-df7b-41d4-804e-0a56d9e2c9fb

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_MainTheoremFormsStatement
import Definitions.Def_VariableBound_Paper_Arith
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Definitions.Def_Wrap_Arith
import Theorems.Thm_Wrap_Arith_rate_le_const_add

set_option autoImplicit false
section
section
open Wrap
open MainTheoremForms
open Wrap.Arith
namespace Wrap.Arith
theorem _root_.solution {B ε : ℝ} (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ c : ℕ, ∀ n : ℕ, 4 ≤ n → (2 : ℝ) ^ (B * ((n : ℝ) * lg (lg n) / Real.sqrt (lg n))) ≤ (c : ℝ) * (2 : ℝ) ^ (ε * n) := by
  obtain ⟨n₀, hn₀⟩ := exists_nat_ge ((2 : ℝ) ^ ((8 * B / ε) ^ 4))
  obtain ⟨c, hc⟩ := exists_nat_ge ((2 : ℝ) ^ (8 * B * n₀))
  refine ⟨c, fun n hn => ?_⟩
  calc (2 : ℝ) ^ (B * ((n : ℝ) * lg (lg n) / Real.sqrt (lg n))) ≤ (2 : ℝ) ^ (8 * B * n₀ + ε * n) :=
        Real.rpow_le_rpow_of_exponent_le one_le_two (rate_le_const_add hB hε hn₀ hn)
    _ = (2 : ℝ) ^ (8 * B * n₀) * (2 : ℝ) ^ (ε * n) := Real.rpow_add two_pos _ _
    _ ≤ (c : ℝ) * (2 : ℝ) ^ (ε * n) := mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg zero_le_two _)
end Wrap.Arith

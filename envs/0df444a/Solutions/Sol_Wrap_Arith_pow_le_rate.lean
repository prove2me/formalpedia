-- Prove2me | solution 1 for Wrap.Arith.pow_le_rate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:56:20.41821+00:00
-- url     : https://prove2.me/submissions/5fc8b226-069e-4303-a7cf-6985d208d165

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_MainTheoremFormsStatement
import Definitions.Def_Wrap_Arith
import Definitions.Def_VariableBound_Paper_Arith
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Definitions.Def_Wrap_ArithRate
import Theorems.Thm_Wrap_Arith_lg_le_rate

set_option autoImplicit false
section
section
open Wrap
open MainTheoremForms
open Wrap.Arith
namespace Wrap.Arith
theorem _root_.solution (D n : ℕ) : ((n : ℝ) + 2) ^ D ≤ (2 : ℝ) ^ ((D : ℝ) * (64 * ((n : ℝ) * SatK.rN 1 (1 / 2) n) + 256)) := by
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hN : (0 : ℝ) < (n : ℝ) + 4 := by positivity
  have e : (2 : ℝ) ^ lg ((n : ℝ) + 4) = (n : ℝ) + 4 := Real.rpow_logb two_pos (by norm_num) hN
  calc ((n : ℝ) + 2) ^ D ≤ ((n : ℝ) + 4) ^ D := pow_le_pow_left₀ (by positivity) (by linarith) D
    _ = (2 : ℝ) ^ ((D : ℝ) * lg ((n : ℝ) + 4)) := by
        rw [mul_comm, Real.rpow_mul zero_le_two, e, Real.rpow_natCast]
    _ ≤ (2 : ℝ) ^ ((D : ℝ) * (64 * ((n : ℝ) * SatK.rN 1 (1 / 2) n) + 256)) :=
        Real.rpow_le_rpow_of_exponent_le one_le_two (mul_le_mul_of_nonneg_left (lg_le_rate n) (Nat.cast_nonneg D))
end Wrap.Arith

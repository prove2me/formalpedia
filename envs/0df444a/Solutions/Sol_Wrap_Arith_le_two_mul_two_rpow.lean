-- Prove2me | solution 1 for Wrap.Arith.le_two_mul_two_rpow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:55:08.208481+00:00
-- url     : https://prove2.me/submissions/2314db86-4dde-485a-a6be-71924fcbb60f

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
import Theorems.Thm_Wrap_Arith_half_lt_log_two

set_option autoImplicit false
section
section
open Wrap
open MainTheoremForms
open Wrap.Arith
namespace Wrap.Arith
theorem _root_.solution {s : ℝ} (hs : 0 ≤ s) : s ≤ 2 * (2 : ℝ) ^ s := by
  have h2 := half_lt_log_two
  have h1 : s * Real.log 2 + 1 ≤ Real.exp (s * Real.log 2) := Real.add_one_le_exp _
  have e : (2 : ℝ) ^ s = Real.exp (s * Real.log 2) := by
    rw [Real.rpow_def_of_pos two_pos, mul_comm]
  rw [e]
  nlinarith
end Wrap.Arith

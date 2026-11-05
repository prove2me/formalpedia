-- Prove2me | solution 1 for Wrap.Arith.lg_le_fourth_root
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:01:45.826716+00:00
-- url     : https://prove2.me/submissions/238cca08-9085-478b-bfaa-c0e72dba1638

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
theorem _root_.solution {y : ℝ} (hy : 0 < y) : lg y ≤ 8 * Real.sqrt (Real.sqrt y) := by
  have h2 := half_lt_log_two
  have hw : 0 < Real.sqrt (Real.sqrt y) := Real.sqrt_pos.2 (Real.sqrt_pos.2 hy)
  have hy4 : Real.sqrt (Real.sqrt y) ^ 4 = y := by
    calc Real.sqrt (Real.sqrt y) ^ 4 = (Real.sqrt (Real.sqrt y) ^ 2) ^ 2 := by ring
      _ = Real.sqrt y ^ 2 := by rw [Real.sq_sqrt (Real.sqrt_nonneg y)]
      _ = y := Real.sq_sqrt hy.le
  have hl : Real.log y ≤ 4 * Real.sqrt (Real.sqrt y) := by
    have h1 := Real.log_le_sub_one_of_pos hw
    have h3 : Real.log (Real.sqrt (Real.sqrt y) ^ 4) = 4 * Real.log (Real.sqrt (Real.sqrt y)) := (Real.log_pow _ 4).trans (by norm_num)
    rw [hy4] at h3
    linarith
  unfold lg Real.logb
  rw [div_le_iff₀ (by linarith)]
  nlinarith [mul_pos hw (sub_pos.2 h2)]
end Wrap.Arith

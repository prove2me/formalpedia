-- Prove2me | solution 1 for Wrap.Arith.lg_div_sqrt_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:02:58.949988+00:00
-- url     : https://prove2.me/submissions/c4f33334-b7f2-4353-bf73-2c099a030530

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
import Theorems.Thm_Wrap_Arith_lg_le_fourth_root

set_option autoImplicit false
section
section
open Wrap
open MainTheoremForms
open Wrap.Arith
namespace Wrap.Arith
theorem _root_.solution {y : ℝ} (hy : 0 < y) : lg y / Real.sqrt y ≤ 8 / Real.sqrt (Real.sqrt y) := by
  have hw : 0 < Real.sqrt (Real.sqrt y) := Real.sqrt_pos.2 (Real.sqrt_pos.2 hy)
  rw [div_le_div_iff₀ (Real.sqrt_pos.2 hy) hw]
  calc lg y * Real.sqrt (Real.sqrt y) ≤ 8 * Real.sqrt (Real.sqrt y) * Real.sqrt (Real.sqrt y) :=
        mul_le_mul_of_nonneg_right (lg_le_fourth_root hy) hw.le
    _ = 8 * Real.sqrt y := by rw [mul_assoc, Real.mul_self_sqrt (Real.sqrt_nonneg y)]
end Wrap.Arith

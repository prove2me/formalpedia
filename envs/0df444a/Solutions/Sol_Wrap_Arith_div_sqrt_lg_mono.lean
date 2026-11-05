-- Prove2me | solution 1 for Wrap.Arith.div_sqrt_lg_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:57:29.56926+00:00
-- url     : https://prove2.me/submissions/93f17b97-ced8-46b0-863d-356bc0655fb3

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
import Theorems.Thm_Wrap_Arith_one_le_lg_real
import Theorems.Thm_Wrap_Arith_sq_mul_lg_le

set_option autoImplicit false
section
section
open Wrap
open MainTheoremForms
open Wrap.Arith
namespace Wrap.Arith
theorem _root_.solution {x y : ℝ} (hx : 2 ≤ x) (hxy : x ≤ y) : x / Real.sqrt (lg x) ≤ y / Real.sqrt (lg y) := by
  have hlx := one_le_lg_real hx
  have hly := one_le_lg_real (hx.trans hxy)
  rw [div_le_div_iff₀ (Real.sqrt_pos.2 (by linarith)) (Real.sqrt_pos.2 (by linarith))]
  refine (pow_le_pow_iff_left₀ (mul_nonneg (by linarith) (Real.sqrt_nonneg _)) (mul_nonneg (by linarith) (Real.sqrt_nonneg _)) two_ne_zero).1 ?_
  rw [mul_pow, mul_pow, Real.sq_sqrt (by linarith), Real.sq_sqrt (by linarith)]
  exact sq_mul_lg_le hx hxy
end Wrap.Arith

-- Prove2me | solution 1 for Wrap.Arith.lg_le_two_mul_sub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:55:09.270761+00:00
-- url     : https://prove2.me/submissions/93aa1c18-aae4-4597-893a-d398442c55c6

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
import Theorems.Thm_Wrap_Arith_half_lt_log_two


set_option autoImplicit false
section
section
open Wrap
open MainTheoremForms
open Wrap.Arith
namespace Wrap.Arith
theorem _root_.solution {t : ℝ} (ht : 1 ≤ t) : lg t ≤ 2 * (t - 1) := by
  have h2 := half_lt_log_two
  have hl : Real.log t ≤ t - 1 := Real.log_le_sub_one_of_pos (by linarith)
  unfold lg Real.logb
  rw [div_le_iff₀ (by linarith)]
  nlinarith [mul_nonneg (sub_nonneg.2 ht) (sub_pos.2 h2).le]
end Wrap.Arith

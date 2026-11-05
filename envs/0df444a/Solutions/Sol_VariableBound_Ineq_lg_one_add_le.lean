-- Prove2me | solution 1 for VariableBound.Ineq.lg_one_add_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:55:05.659021+00:00
-- url     : https://prove2.me/submissions/091b7137-76fc-4f9c-9cf9-32db5e41bc21

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Params_Defs
import Definitions.Def_ClauseBound_ParityChecks_Binom
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_VariableBound_Params_Ineq

set_option autoImplicit false
section
section
open VariableBound
open AppVariables
open VariableBound.Ineq
namespace VariableBound.Ineq
theorem _root_.solution {p : ℝ} (hp : 0 ≤ p) : lg (1 + p) ≤ 3 / 2 * p := by
  have h1 : Real.log (1 + p) ≤ p := by
    have := Real.log_le_sub_one_of_pos (x := 1 + p) (by linarith)
    linarith
  have h2 := Real.log_two_gt_d9
  unfold lg Real.logb
  rw [div_le_iff₀ (by linarith)]
  nlinarith
end VariableBound.Ineq

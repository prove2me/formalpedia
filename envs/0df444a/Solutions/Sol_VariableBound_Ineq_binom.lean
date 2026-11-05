-- Prove2me | solution 1 for VariableBound.Ineq.binom
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:55:59.034595+00:00
-- url     : https://prove2.me/submissions/167d7f01-8e90-46b1-880a-7ff1220f6ac2

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Params_Defs
import Definitions.Def_ClauseBound_ParityChecks_Binom
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_VariableBound_Params_Ineq
import Theorems.Thm_ClauseBound_ParityChecks_logb_choose_le


set_option autoImplicit false
section
section
open VariableBound
open AppVariables
open VariableBound.Ineq
namespace VariableBound.Ineq
theorem _root_.solution {t μ μ' : ℕ} (h : μ ≤ μ') (h1 : 1 ≤ μ') : lg (t.choose μ) ≤ μ' * max 1 (lg (3 * t / μ')) := ClauseBound.ParityChecks.logb_choose_le h h1
end VariableBound.Ineq

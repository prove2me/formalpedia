-- Prove2me | solution 1 for VariableBound.StepParity.ev_le_one
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-04T23:19:47.193459+00:00
-- url     : https://prove2.me/submissions/e2a70c7c-9415-4a18-9641-af5901c0a26d

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_AppVariablesStatement
import Definitions.Def_ClauseBound_ParityChecks_StepOne
import Definitions.Def_ClauseBound_ParityChecks_StepOne
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.List.GetD
import Definitions.Def_VariableBound_StepParity
set_option autoImplicit false
section
section
open VariableBound VariableBound.StepParity
open Finset ParityChecks AppVariables
variable {X E : Type} [DecidableEq E]

theorem solution (q : ℕ) : ev q ≤ 1 := by
  unfold ParityChecks.ev
  split_ifs <;> norm_num

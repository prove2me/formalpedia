-- Prove2me | solution 1 for QueryMachines.QueryMachine.close_step_none
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:54:07.504107+00:00
-- url     : https://prove2.me/submissions/77651fe3-8427-468d-b76a-dff6919dcb95

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_QueryMachines_Kernel
import Definitions.Def_StepMachines_Prog_Stepped
import Mathlib.Tactic
import Definitions.Def_QueryMachines_Runs

set_option autoImplicit false
section
section
open QueryMachines QueryMachines.QueryMachine
open Groundwork
variable {Q A Q' A' C α β : Type}
namespace QueryMachines.QueryMachine
theorem _root_.solution {M : QueryMachine Q A α β} {O : Q → Option A} {s : M.σ} (h : M.ask s = none) : (M.close O).step s = M.step s := by
  change (match M.ask s with | some x => _ | none => _) = _
  rw [h]
end QueryMachines.QueryMachine

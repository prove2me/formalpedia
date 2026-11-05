-- Prove2me | solution 1 for QueryMachines.QueryMachine.close_step_some
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:54:08.458388+00:00
-- url     : https://prove2.me/submissions/fb004d06-fcdd-4285-b92a-0f5a813ccc19

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
theorem _root_.solution {M : QueryMachine Q A α β} {O : Q → Option A} {s : M.σ} {x : Q} {v : A} (h : M.ask s = some x) (hv : O x = some v) :
    (M.close O).step s = M.resume s v := by
  change (match M.ask s with | some x => (match O x with | some v => _ | none => _) | none => _) = _
  rw [h]
  change (match O x with | some v => _ | none => _) = _
  rw [hv]
end QueryMachines.QueryMachine

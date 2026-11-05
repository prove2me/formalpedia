-- Prove2me | solution 1 for QueryMachines.QueryMachine.close_step_stuck
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:02:57.550208+00:00
-- url     : https://prove2.me/submissions/85d65543-adb8-4a1e-a17a-1c4bd6023034

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
theorem _root_.solution {M : QueryMachine Q A α β} {O : Q → Option A} {s : M.σ} {x : Q} (h : M.ask s = some x) (hv : O x = none) :
    (M.close O).step s = s := by
  change (match M.ask s with | some x => (match O x with | some v => _ | none => _) | none => _) = _
  rw [h]
  change (match O x with | some v => _ | none => _) = _
  rw [hv]
end QueryMachines.QueryMachine

-- Prove2me | solution 1 for QueryMachines.QueryMachine.reaches_asksNothing
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:54:18.721084+00:00
-- url     : https://prove2.me/submissions/12098d8b-ceb6-4bef-bd04-0f1cb9f260bf

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
theorem _root_.solution {R : Stepped α β} {O : Q → Option A} {S t : ℕ} {b : β} {s : R.σ} (h : R.Reaches S b s t) :
    ({ R with ask := fun _ => none, resume := fun s _ => s } : QueryMachine Q A α β).Reaches O S b s t [] := by
  induction h with
  | halt ho hs => exact .halt ho hs
  | step ho hs _ ih => exact .step ho rfl hs ih
end QueryMachines.QueryMachine

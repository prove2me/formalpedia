-- Prove2me | solution 1 for QueryMachines.QueryMachine.toStepped_reaches
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:03:35.040115+00:00
-- url     : https://prove2.me/submissions/5486229b-9269-4a7b-a204-9d3ac3bda624

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
theorem _root_.solution {M : QueryMachine Q A α β} {O : Q → Option A} {S own : ℕ} {L : List Q} {b : β} {s : M.σ} (h : M.Reaches O S b s own L) (hL : L = []) :
    M.toStepped.Reaches S b s own := by
  induction h with
  | halt ho hs => exact .halt ho hs
  | step ho _ hs _ ih => exact .step ho hs (ih hL)
  | query _ _ _ _ _ _ => cases hL
end QueryMachines.QueryMachine

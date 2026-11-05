-- Prove2me | solution 1 for QueryMachines.QueryMachine.Runs.mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:50:14.727402+00:00
-- url     : https://prove2.me/submissions/d3e86593-0be9-4829-9d5c-7344b4027832

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_QueryMachines_Kernel
import Definitions.Def_StepMachines_Prog_Stepped
import Mathlib.Tactic
import Definitions.Def_QueryMachines_Runs
import Theorems.Thm_QueryMachines_QueryMachine_Reaches_mono
import Theorems.Thm_Groundwork_Stepped_Reaches_mono
import Theorems.Thm_Groundwork_Stepped_Runs_mono
import Theorems.Thm_Groundwork_TM_Frag_Within_mono


set_option autoImplicit false
section
section
open QueryMachines QueryMachines.QueryMachine
open Groundwork
variable {Q A Q' A' C α β : Type}
namespace QueryMachines.QueryMachine
namespace Runs
theorem _root_.solution {M : QueryMachine Q A α β} {O : Q → Option A} {S S' own own' : ℕ} {L : List Q} {b : β} {a : α}
    (h : M.Runs O a own L S b) (ho : own ≤ own') (hS : S ≤ S') : M.Runs O a own' L S' b := Reaches.mono h ho hS
end Runs
end QueryMachines.QueryMachine

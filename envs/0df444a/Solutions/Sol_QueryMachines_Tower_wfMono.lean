-- Prove2me | solution 1 for QueryMachines.Tower.wfMono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:53:34.694412+00:00
-- url     : https://prove2.me/submissions/a8337ca6-e542-4ab8-b1ff-866c4557c6d2

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_QueryMachines_Runs
import Definitions.Def_Tower_Kernel
import Theorems.Thm_Groundwork_Stepped_Reaches_mono
import Theorems.Thm_Groundwork_Stepped_Runs_mono
import Theorems.Thm_Groundwork_TM_Frag_Within_mono
import Theorems.Thm_QueryMachines_QueryMachine_Reaches_mono
import Theorems.Thm_QueryMachines_QueryMachine_Runs_mono
import Theorems.Thm_QueryMachines_QueryMachine_WithinFrom_mono
import Theorems.Thm_QueryMachines_QueryMachine_Within_mono


set_option autoImplicit false
section
section
open QueryMachines QueryMachines.Tower
open Groundwork
variable {Q A α β : Type} {M : QueryMachine Q A α β} {O : Q → Option A} {w : Q → ℕ} {s : M.σ} {b : β} {S S' T T' : ℕ}
namespace QueryMachines.Tower
theorem _root_.solution (h : M.WithinFrom O w s T S b) (hT : T ≤ T') (hS : S ≤ S') : M.WithinFrom O w s T' S' b := QueryMachine.WithinFrom.mono h hT hS
end QueryMachines.Tower

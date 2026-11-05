-- Prove2me | solution 1 for QueryMachines.QueryMachine.WithinFrom.mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:51:17.151897+00:00
-- url     : https://prove2.me/submissions/0a26aa80-4289-4d2e-9bf0-704638c392ab

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_QueryMachines_Kernel
import Definitions.Def_StepMachines_Prog_Stepped
import Mathlib.Tactic
import Definitions.Def_QueryMachines_Runs
import Theorems.Thm_QueryMachines_QueryMachine_Reaches_mono
import Theorems.Thm_QueryMachines_QueryMachine_Runs_mono
import Theorems.Thm_Groundwork_Stepped_Reaches_mono
import Theorems.Thm_Groundwork_Stepped_Runs_mono
import Theorems.Thm_Groundwork_TM_Frag_Within_mono
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
open QueryMachines QueryMachines.QueryMachine
open Groundwork
variable {Q A Q' A' C α β : Type}
namespace QueryMachines.QueryMachine
namespace WithinFrom
theorem _root_.solution {M : QueryMachine Q A α β} {O : Q → Option A} {w : Q → ℕ} {S S' T T' : ℕ} {b : β} {s : M.σ}
    (h : M.WithinFrom O w s T S b) (hT : T ≤ T') (hS : S ≤ S') : M.WithinFrom O w s T' S' b :=
  let ⟨own, L, hr, hle⟩ := h; ⟨own, L, hr.mono le_rfl hS, hle.trans hT⟩
end WithinFrom
end QueryMachines.QueryMachine

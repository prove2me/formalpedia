-- Prove2me | solution 1 for QueryMachines.stClose
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:05:54.07948+00:00
-- url     : https://prove2.me/submissions/1be85488-e4a9-4584-8582-8db0673bedfb

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_QueryMachines_Kernel
import Definitions.Def_StepMachines_Prog_Stepped
import Mathlib.Tactic
import Definitions.Def_QueryMachines_Runs
import Theorems.Thm_QueryMachines_QueryMachine_Reaches_mono
import Theorems.Thm_QueryMachines_QueryMachine_Runs_mono
import Theorems.Thm_QueryMachines_QueryMachine_WithinFrom_mono
import Theorems.Thm_QueryMachines_QueryMachine_Within_mono
import Theorems.Thm_QueryMachines_QueryMachine_sum_map_unitCost
import Theorems.Thm_QueryMachines_QueryMachine_reaches_of_close
import Theorems.Thm_QueryMachines_QueryMachine_close_reaches
import Theorems.Thm_Groundwork_Stepped_Reaches_mono
import Theorems.Thm_Groundwork_Stepped_Runs_mono
import Theorems.Thm_Groundwork_TM_Frag_Within_mono


set_option autoImplicit false
section
section
open QueryMachines
open Groundwork QueryMachine
namespace QueryMachines
theorem _root_.solution : StClose := fun _ _ _ _ _ _ _ _ _ _ =>
  ⟨fun h => let ⟨own, L, hr, hle⟩ := reaches_of_close h; ⟨own, L, hr, by rw [sum_map_unitCost]; exact hle⟩,
   fun ⟨own, L, hr, hle⟩ => (close_reaches hr).mono (by rw [sum_map_unitCost] at hle; exact hle) le_rfl⟩
end QueryMachines

-- Prove2me | solution 1 for QueryMachines.stQueriesLe
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:54:19.712104+00:00
-- url     : https://prove2.me/submissions/7e0455e8-018f-44bd-8980-ab574ae5a9ba

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_QueryMachines_Kernel
import Definitions.Def_StepMachines_Prog_Stepped
import Mathlib.Tactic
import Definitions.Def_QueryMachines_Runs
import Theorems.Thm_QueryMachines_QueryMachine_sum_map_unitCost

set_option autoImplicit false
section
section
open QueryMachines
open Groundwork QueryMachine
namespace QueryMachines
theorem _root_.solution : StQueriesLe := fun _ _ _ _ _ _ _ _ _ _ ⟨own, L, hr, hle⟩ => ⟨own, L, hr, by rw [sum_map_unitCost] at hle; exact hle⟩
end QueryMachines

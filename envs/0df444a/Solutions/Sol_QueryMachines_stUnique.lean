-- Prove2me | solution 1 for QueryMachines.stUnique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:04:39.578437+00:00
-- url     : https://prove2.me/submissions/1bbb6335-b6d4-4317-a82d-fecab2b95c85

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_QueryMachines_Kernel
import Definitions.Def_StepMachines_Prog_Stepped
import Mathlib.Tactic
import Definitions.Def_QueryMachines_Runs
import Theorems.Thm_QueryMachines_QueryMachine_Reaches_unique
import Theorems.Thm_Groundwork_Stepped_Runs_unique


set_option autoImplicit false
section
section
open QueryMachines
open Groundwork QueryMachine
namespace QueryMachines
theorem _root_.solution : StUnique := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h h' => Reaches.unique h h'
end QueryMachines

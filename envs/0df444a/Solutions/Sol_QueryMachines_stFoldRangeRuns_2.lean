-- Prove2me | solution 2 for QueryMachines.stFoldRangeRuns
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:21:59.790769+00:00
-- url     : https://prove2.me/submissions/1ec0a86f-16db-4619-b8e3-cda77775c189

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_QueryMachines_CombRunsStatement
import Definitions.Def_QueryMachines_Runs
import Mathlib.Tactic
import Definitions.Def_QueryMachines_CombRuns
import Theorems.Thm_QueryMachines_QueryMachine_foldRange_runs
import Theorems.Thm_Groundwork_Stepped_foldRange_runs


set_option autoImplicit false
section
section
open QueryMachines
open Groundwork Finset QueryMachine
namespace QueryMachines
theorem _root_.solution : StFoldRangeRuns := fun _ _ _ _ _ _ _ _ _ _ _ _ _ t Lq v Sc Sm hM hc => foldRange_runs t Lq v Sc Sm hM hc
end QueryMachines

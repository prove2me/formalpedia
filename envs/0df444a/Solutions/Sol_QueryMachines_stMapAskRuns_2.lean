-- Prove2me | solution 2 for QueryMachines.stMapAskRuns
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:10:52.845959+00:00
-- url     : https://prove2.me/submissions/057f0288-e26a-401b-9392-49a2a4ba2605

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_QueryMachines_CombRunsStatement
import Definitions.Def_QueryMachines_Runs
import Mathlib.Tactic
import Definitions.Def_QueryMachines_CombRuns
import Theorems.Thm_QueryMachines_QueryMachine_mapAsk_reaches

set_option autoImplicit false
section
section
open QueryMachines
open Groundwork Finset QueryMachine
namespace QueryMachines
theorem _root_.solution : StMapAskRuns := fun _ _ _ _ _ _ _ _ _ _ _ _ _ h => mapAsk_reaches h
end QueryMachines

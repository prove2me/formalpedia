-- Prove2me | solution 1 for QueryMachines.Bridge.solverOfMachinePoly
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:42:53.766282+00:00
-- url     : https://prove2.me/submissions/1c609503-cede-45ba-8652-3cb35825e6bc

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedToPadded_Defs
import Definitions.Def_CountedToPadded_RunFor
import Definitions.Def_CountedToPadded_TablesValue
import Definitions.Def_CountedToPadded_Tables
import Definitions.Def_CountedToPadded_Need
import Definitions.Def_CountedToPadded_Pick
import Definitions.Def_CountedToPadded_SolverPoly
import Definitions.Def_CountedToPadded_Levels
import Definitions.Def_QueryMachines_Runs
import Definitions.Def_CountedToPadded_Main
import Theorems.Thm_QueryMachines_Bridge_runForPoly
import Theorems.Thm_QueryMachines_Bridge_solverOfMachinePolyFrom


set_option autoImplicit false
section
section
open QueryMachines QueryMachines.Bridge
namespace QueryMachines.Bridge
theorem _root_.solution : SolverOfMachinePoly := solverOfMachinePolyFrom runForPoly
end QueryMachines.Bridge

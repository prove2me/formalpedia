-- Prove2me | solution 1 for ThmVariables.solverFromMachine
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:04:39.448463+00:00
-- url     : https://prove2.me/submissions/fc7e4247-1796-40ae-bdb0-f2b4cb1f5b7b

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThmVariables_Defs
import Definitions.Def_ThmVariables_Bound
import Definitions.Def_ThmVariables_PartA
import Definitions.Def_ThmVariables_EveryMachine
import Definitions.Def_CountedToPadded_Main
import Definitions.Def_RecursionToBound_Main
import Definitions.Def_ThmVariables_Main
import Theorems.Thm_QueryMachines_Bridge_solverOfMachineLevels
import Theorems.Thm_ThmVariables_solverFromMachine_of


set_option autoImplicit false
section
section
open ThmVariables
open QueryMachines.Bridge
namespace ThmVariables
theorem _root_.solution : SolverFromMachine := solverFromMachine_of solverOfMachineLevels
end ThmVariables

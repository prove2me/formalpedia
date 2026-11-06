-- Prove2me | solution 1 for ThmVariables.partAForEveryMachine
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:45:58.112665+00:00
-- url     : https://prove2.me/submissions/4c6231eb-782e-4dcc-aa82-43c43310f29b

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
import Theorems.Thm_RecursionToBound_thmVariablesAForEveryMachine
import Theorems.Thm_ThmVariables_partAForEveryMachineFrom


set_option autoImplicit false
section
section
open ThmVariables
open QueryMachines.Bridge
namespace ThmVariables
theorem _root_.solution : PartAForEveryMachine := partAForEveryMachineFrom solverOfMachineLevels RecursionToBound.thmVariablesAForEveryMachine
end ThmVariables

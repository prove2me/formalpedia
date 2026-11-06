-- Prove2me | solution 1 for QueryMachines.Bridge.solverOfMachineLevels
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:03:53.203198+00:00
-- url     : https://prove2.me/submissions/d8607ff1-7dd7-4f86-a511-cba0c5aa2744

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
import Theorems.Thm_QueryMachines_Bridge_solverOfMachinePoly
import Theorems.Thm_QueryMachines_Bridge_bitsOfTablesFacts
import Theorems.Thm_QueryMachines_Bridge_cutNumberFacts
import Theorems.Thm_QueryMachines_Bridge_needIsSmall
import Theorems.Thm_QueryMachines_Bridge_needSuffices
import Theorems.Thm_QueryMachines_Bridge_pickOfFacts
import Theorems.Thm_QueryMachines_Bridge_runForIsRight
import Theorems.Thm_QueryMachines_Bridge_solverOfMachineLevelsFrom
import Theorems.Thm_QueryMachines_Bridge_tablesValue
import Theorems.Thm_QueryMachines_stPlug


set_option autoImplicit false
section
section
open QueryMachines QueryMachines.Bridge
namespace QueryMachines.Bridge
theorem _root_.solution : SolverOfMachineLevels :=
  solverOfMachineLevelsFrom stPlug runForIsRight tablesValue bitsOfTablesFacts cutNumberFacts needSuffices needIsSmall solverOfMachinePoly pickOfFacts
end QueryMachines.Bridge

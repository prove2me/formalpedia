-- Prove2me | solution 1 for ThmVariables.partA
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:52:54.822593+00:00
-- url     : https://prove2.me/submissions/6ca9381f-4ac2-4819-98ec-5c94ee04bb6f

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
import Theorems.Thm_ThmVariables_partAForEveryMachine
import Theorems.Thm_ThmVariables_partAFromEveryMachine


set_option autoImplicit false
section
section
open ThmVariables
open QueryMachines.Bridge
namespace ThmVariables
theorem _root_.solution : PartA := partAFromEveryMachine partAForEveryMachine
end ThmVariables

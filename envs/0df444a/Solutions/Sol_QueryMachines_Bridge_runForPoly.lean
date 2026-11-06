-- Prove2me | solution 1 for QueryMachines.Bridge.runForPoly
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:23:34.828018+00:00
-- url     : https://prove2.me/submissions/c58a969a-2969-479e-9ce3-68caa1794fa2

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedToPadded_Defs
import Definitions.Def_CountedToPadded_Compare
import Definitions.Def_ToTuring_Closure_Fold
import Definitions.Def_ToTuring_Lib_List1b
import Definitions.Def_CountedToPadded_RunFor
import Theorems.Thm_QueryMachines_Bridge_everyWordIsCompared
import Theorems.Thm_QueryMachines_Bridge_runForPolyFrom

set_option autoImplicit false
section
section
open QueryMachines QueryMachines.Bridge
open Groundwork Groundwork.PolyT PaddedDescent.F Proof
namespace QueryMachines.Bridge
theorem _root_.solution : RunForPoly := runForPolyFrom everyWordIsCompared
end QueryMachines.Bridge

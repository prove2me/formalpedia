-- Prove2me | solution 1 for QueryMachines.Bridge.everyWordIsCompared
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:14:45.881087+00:00
-- url     : https://prove2.me/submissions/0fc985f8-b3db-454f-a9fd-a213a877422b

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedToPadded_Defs
import Definitions.Def_CountedToPadded_Compare
import Definitions.Def_ToTuring_Closure_Fold
import Definitions.Def_ToTuring_Lib_List1b
import Definitions.Def_CountedToPadded_RunFor
import Theorems.Thm_QueryMachines_Bridge_Proof_wordCompared


set_option autoImplicit false
section
section
open QueryMachines QueryMachines.Bridge
open Groundwork Groundwork.PolyT PaddedDescent.F Proof
namespace QueryMachines.Bridge
theorem _root_.solution : EveryWordIsCompared := fun α _ => wordCompared α
end QueryMachines.Bridge

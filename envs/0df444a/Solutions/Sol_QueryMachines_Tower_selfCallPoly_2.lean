-- Prove2me | solution 2 for QueryMachines.Tower.selfCallPoly
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:19:59.082872+00:00
-- url     : https://prove2.me/submissions/f48f0c6d-a644-4789-b59f-d55ecb60bbd3

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Tower_Defs
import Definitions.Def_QueryMachines_Poly
import Definitions.Def_ToTuring_Lib_List1b
import Definitions.Def_Tower_Poly

set_option autoImplicit false
section
section
open QueryMachines QueryMachines.Tower
open Groundwork Groundwork.PolyT QueryMachines.QueryMachine
namespace QueryMachines.Tower
theorem _root_.solution : SelfCallPoly := fun _ _ _ _ _ _ _ _ M ⟨h⟩ => ⟨@selfCallIsPoly _ _ _ _ _ _ _ _ M h⟩
end QueryMachines.Tower

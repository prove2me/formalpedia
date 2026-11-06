-- Prove2me | solution 1 for QueryMachines.Tower.Toy.toyPoly
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:59:29.479214+00:00
-- url     : https://prove2.me/submissions/7703f469-e914-41e2-aa4b-ec27e8499eb9

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Tower_Toy_Defs
import Definitions.Def_Tower_PolyTower
import Definitions.Def_ToTuring_Lib_Nat1
import Definitions.Def_Tower_Toy_Machines
import Theorems.Thm_QueryMachines_Tower_towerPoly


set_option autoImplicit false
section
section
open QueryMachines QueryMachines.Tower QueryMachines.Tower.Toy
open Groundwork Groundwork.PolyT QueryMachines.QueryMachine
namespace QueryMachines.Tower.Toy
theorem _root_.solution : ToyPoly := towerPoly _ _ _ _ Sol Inn ⟨solIsPoly⟩ ⟨innIsPoly⟩
end QueryMachines.Tower.Toy

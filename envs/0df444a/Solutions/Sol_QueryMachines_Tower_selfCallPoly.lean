-- Prove2me | solution 1 for QueryMachines.Tower.selfCallPoly
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-04T23:22:27.641509+00:00
-- url     : https://prove2.me/submissions/f55a475d-32cd-43f3-8342-0ba994648447

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

theorem solution : SelfCallPoly := by
  intro Q A α β _ _ _ _ M hM
  obtain ⟨hM⟩ := hM
  letI : IsPolyQ M := hM
  exact ⟨selfCallIsPoly M⟩

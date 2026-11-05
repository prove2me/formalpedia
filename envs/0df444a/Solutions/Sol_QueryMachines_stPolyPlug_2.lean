-- Prove2me | solution 2 for QueryMachines.stPolyPlug
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-04T22:28:24.180997+00:00
-- url     : https://prove2.me/submissions/81ebc789-f306-4d55-9f6b-dcbab0445308

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_QueryMachines_Comb
import Definitions.Def_ToTuring_Poly_Range
import Definitions.Def_ToTuring_Poly_Comb
import Mathlib.Tactic
import Definitions.Def_QueryMachines_Poly

set_option autoImplicit false
section
section
open QueryMachines
open Groundwork QueryMachine

theorem solution : StPolyPlug :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ M R ⟨_hM⟩ ⟨_hR⟩ => ⟨plug_isPolyT M R⟩

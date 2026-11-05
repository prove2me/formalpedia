-- Prove2me | solution 1 for QueryMachines.stPolyPlug
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T21:59:26.111909+00:00
-- url     : https://prove2.me/submissions/2da88535-ab80-49cc-a058-6561cea45304

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
namespace QueryMachines
theorem _root_.solution : StPolyPlug := fun _ _ _ _ _ _ _ _ _ _ _ _ M R ⟨_hM⟩ ⟨_hR⟩ => ⟨plug_isPolyT M R⟩
end QueryMachines

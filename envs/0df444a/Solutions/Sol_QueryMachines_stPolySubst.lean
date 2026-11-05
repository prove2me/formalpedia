-- Prove2me | solution 1 for QueryMachines.stPolySubst
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T21:58:13.13295+00:00
-- url     : https://prove2.me/submissions/22a54443-175f-4e71-8a13-b5b795b900c6

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
theorem _root_.solution : StPolySubst := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ M N ⟨_hM⟩ ⟨_hN⟩ => ⟨subst_isPolyQ M N⟩
end QueryMachines

-- Prove2me | solution 1 for TwoMachines.out_haltList
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:06:29.550538+00:00
-- url     : https://prove2.me/submissions/0a80a338-8cc1-436b-8778-a7d57788698b

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_TwoMachines_Defs
import Definitions.Def_Wrap_CodingExists
import Definitions.Def_CircuitLowerBound_Tab_Sound
import Definitions.Def_CountKSat_Host
import Definitions.Def_ToTuring_Poly_Comb
import Definitions.Def_ToTuring_Closure_Basic
import Definitions.Def_ToTuring_Closure_Cases
import Definitions.Def_ToTuring_Lib_List1b
import Definitions.Def_TwoMachines_Main
import Theorems.Thm_CircuitLowerBound_Tab_haltList_stk_self
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.map



set_option autoImplicit false
section
section
open TwoMachines
open Turing Groundwork Wrap CircuitLowerBound.Tab
variable {M₁ M₂ : TM2ComputableAux Bool Bool}
namespace TwoMachines
theorem _root_.solution {M : TM2ComputableAux Bool Bool} (K : Coding M) (y : List Bool) : K.out (K.rep (haltList M.tm (y.map M.outputAlphabet.invFun))) = some y := by
  rw [K.out_halted _ rfl, haltList_stk_self, List.map_map]
  have e : (M.outputAlphabet ∘ M.outputAlphabet.invFun) = id := funext fun b => M.outputAlphabet.right_inv b
  rw [e, List.map_id]
end TwoMachines

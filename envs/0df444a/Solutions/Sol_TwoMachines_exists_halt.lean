-- Prove2me | solution 1 for TwoMachines.exists_halt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:05:45.842699+00:00
-- url     : https://prove2.me/submissions/2c9c2bd1-ae92-44c0-908c-06a2db3baa56

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
import Theorems.Thm_CircuitLowerBound_Tab_stay_of_evals
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.map



set_option autoImplicit false
section
section
open TwoMachines
open Turing Groundwork Wrap CircuitLowerBound.Tab
variable {M₁ M₂ : TM2ComputableAux Bool Bool}
namespace TwoMachines
theorem _root_.solution {M : TM2ComputableAux Bool Bool} {x y : List Bool} {t : ℕ} (h : Outputs M x y t) :
    ∃ n ≤ t, (stay M)^[n] (start M x) = haltList M.tm (y.map M.outputAlphabet.invFun) := by
  obtain ⟨ev⟩ := h
  exact ⟨ev.steps, ev.steps_le_m, stay_of_evals M ev.steps ev.evals_in_steps⟩
end TwoMachines

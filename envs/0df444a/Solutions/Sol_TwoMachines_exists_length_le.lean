-- Prove2me | solution 1 for TwoMachines.exists_length_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T20:55:25.559571+00:00
-- url     : https://prove2.me/submissions/e375f2ef-e281-4db3-9cfa-bcb03731d0a6

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
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_Groundwork_length_le_len
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open TwoMachines
open Turing Groundwork Wrap CircuitLowerBound.Tab
variable {M₁ M₂ : TM2ComputableAux Bool Bool}
namespace TwoMachines
theorem _root_.solution {pre : List Bool → List Bool} (hpre : PolyT pre) : ∃ c : ℕ, ∀ x : List Bool, (pre x).length ≤ c * (3 * x.length + 2 + 1) ^ c := by
  obtain ⟨-, c, -, hc⟩ := hpre
  refine ⟨c, fun x => ?_⟩
  have := hc x
  rw [len_bools x] at this
  exact (length_le_len _).trans this
end TwoMachines

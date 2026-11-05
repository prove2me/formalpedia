-- Prove2me | solution 1 for TwoMachines.eq_of_halted
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:06:09.758436+00:00
-- url     : https://prove2.me/submissions/bec73132-e478-4555-af7c-a1ee064847c8

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
import Theorems.Thm_CircuitLowerBound_Tab_iterate_stay_of_halted


set_option autoImplicit false
section
section
open TwoMachines
open Turing Groundwork Wrap CircuitLowerBound.Tab
variable {M₁ M₂ : TM2ComputableAux Bool Bool}
namespace TwoMachines
theorem _root_.solution {M : TM2ComputableAux Bool Bool} {c₀ c : M.tm.Cfg} {i n : ℕ} (hi : ((stay M)^[i] c₀).l = none) (hin : i ≤ n) (hn : (stay M)^[n] c₀ = c) : (stay M)^[i] c₀ = c := by
  rw [← hn, show n = (n - i) + i from (Nat.sub_add_cancel hin).symm, Function.iterate_add_apply, iterate_stay_of_halted M hi]
end TwoMachines

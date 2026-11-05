-- Prove2me | solution 1 for TwoMachines.size_rep_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:06:40.204139+00:00
-- url     : https://prove2.me/submissions/3a3e43f2-3f82-4b72-95b6-8ab7bc84d753

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
import Theorems.Thm_Wrap_size_rep_iterate_le
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open TwoMachines
open Turing Groundwork Wrap CircuitLowerBound.Tab
variable {M₁ M₂ : TM2ComputableAux Bool Bool}
namespace TwoMachines
theorem _root_.solution {M : TM2ComputableAux Bool Bool} (K : Coding M) (x : List Bool) {i t : ℕ} (hi : i ≤ t) : size (K.rep ((stay M)^[i] (start M x))) ≤ K.a * (x.length + 1) + K.a * t := by
  have h1 := size_rep_iterate_le K (start M x) i
  have h0 : size (K.rep (start M x)) ≤ K.a * (x.length + 1) := by
    rw [start, ← K.init_rep]
    exact K.size_init _
  have h2 : K.a * i ≤ K.a * t := Nat.mul_le_mul_left _ hi
  omega
end TwoMachines

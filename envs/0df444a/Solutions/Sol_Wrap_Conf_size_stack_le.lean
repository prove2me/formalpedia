-- Prove2me | solution 1 for Wrap.Conf.size_stack_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:00:24.713704+00:00
-- url     : https://prove2.me/submissions/51b4d9fc-0305-4892-b345-24f14c788dcc

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Wrap_Coding
import Definitions.Def_CircuitLowerBound_Tab_Sound
import Definitions.Def_ToTuring_Lib_Table
import Definitions.Def_ToTuring_Lib_List2
import Definitions.Def_ToTuring_Lib_Nat1
import Mathlib.Data.Finite.Sigma
import Mathlib.Tactic.Linarith
import Definitions.Def_Wrap_CodingExists
import Theorems.Thm_Wrap_Conf_size_le_of_forall
import Theorems.Thm_Wrap_Conf_size_sym_le
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map



set_option autoImplicit false
section
section
open Wrap Wrap.Conf
open Turing Groundwork CircuitLowerBound.Tab
variable (M : TM2ComputableAux Bool Bool)
variable [∀ i, Finite (M.tm.Γ i)]
namespace Wrap.Conf
theorem _root_.solution (k : M.tm.K) (S : List (M.tm.Γ k)) : size (S.map (sym M k)) ≤ S.length * (bnd M + 1) + 1 := by
  have := size_le_of_forall (l := S.map (sym M k)) (B := bnd M) fun n hn => by
    obtain ⟨y, -, rfl⟩ := List.mem_map.1 hn
    exact size_sym_le M k y
  rwa [List.length_map] at this
end Wrap.Conf

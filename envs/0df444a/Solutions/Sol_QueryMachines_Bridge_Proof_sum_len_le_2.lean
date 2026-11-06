-- Prove2me | solution 2 for QueryMachines.Bridge.Proof.sum_len_le
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T18:18:06.980469+00:00
-- url     : https://prove2.me/submissions/a7c7a293-5c90-4fb9-b72a-fe4c23da2058

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_PolyT
import Definitions.Def_ToTuring_Closure_Fold
import Definitions.Def_ToTuring_Lib_List1b
import Definitions.Def_ToTuring_Lib_Nat1b
import Definitions.Def_ToTuring_Lib_Bool
import Definitions.Def_CountedToPadded_Compare
import Theorems.Thm_QueryMachines_Bridge_Proof_nodes_pos
import Theorems.Thm_QueryMachines_Bridge_Proof_nodes_le
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_sum
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.sum


set_option autoImplicit false
section
section
open QueryMachines QueryMachines.Bridge QueryMachines.Bridge.Proof
open Turing Groundwork Groundwork.TM Groundwork.PolyT

theorem solution (w : List V) : (w.map fun a => len a + 2).sum ≤ 3 * total w := by
  induction w with
  | nil => simp [total]
  | cons v r ih =>
    have h1 : 1 ≤ (code v).length := (nodes_pos v).trans (nodes_le v)
    have h2 : len v = (code v).length := rfl
    simp only [total, List.map_cons, List.sum_cons] at ih ⊢
    omega

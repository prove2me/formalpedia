-- Prove2me | solution 1 for Suffices.size_clauses_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:26:33.339552+00:00
-- url     : https://prove2.me/submissions/44682815-d85f-49ca-9fa5-ed7008c685e8

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Suffices_Defs
import Definitions.Def_Exits_Tested
import Definitions.Def_StepMachines_Prog_Sat
import Definitions.Def_StepMachines_Prog_Sat
import Mathlib.Tactic.Ring
import Definitions.Def_Suffices_Sizes
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_Prog_size_list_le
import Theorems.Thm_Groundwork_Prog_size_lit_le
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open Suffices
open Groundwork Groundwork.Prog CountKSat Exits
namespace Suffices
theorem _root_.solution {x : Fml} {m k n N : ℕ} (hm : x.length ≤ m) (hx : ∀ C ∈ x, C.length ≤ k ∧ ∀ l ∈ C, l.1 < n) (hk : k ≤ 3) (hn : n ≤ N) (hN : 1 ≤ N) : size x ≤ m * (14 * N) + 1 := by
  have s : size x ≤ m * (k * (n + 2 + 1) + 1 + 1) + 1 := size_list_le hm fun C hC => size_list_le (hx C hC).1 fun l hl => size_lit_le ((hx C hC).2 l hl)
  have a : k * (n + 2 + 1) ≤ 3 * (n + 2 + 1) := Nat.mul_le_mul_right _ hk
  have b : m * (k * (n + 2 + 1) + 1 + 1) ≤ m * (14 * N) := Nat.mul_le_mul_left _ (by omega)
  omega
end Suffices

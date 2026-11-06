-- Prove2me | solution 1 for Suffices.size_stack_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:46:02.178809+00:00
-- url     : https://prove2.me/submissions/05d79825-df2e-4635-a1f1-4237773043db

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
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open Suffices
open Groundwork Groundwork.Prog CountKSat Exits
namespace Suffices
theorem _root_.solution {st : List CNode} {D n N : ℕ} (hl : st.length ≤ D * n + 1) (hx : ∀ x ∈ st, size x ≤ 142 * N ^ 2) (hn : n ≤ N) (hN : 1 ≤ N) : size st ≤ (143 * (D + 1) + 1) * N ^ 3 := by
  have s := size_list_le hl hx
  have hN2 : 1 ≤ N ^ 2 := Nat.one_le_pow _ _ hN
  have hN3 : 1 ≤ N ^ 3 := Nat.one_le_pow _ _ hN
  have p1 : D * n + 1 ≤ (D + 1) * N := by
    have a1 : D * n ≤ D * N := Nat.mul_le_mul_left _ hn
    have a3 : (D + 1) * N = D * N + N := by ring
    omega
  have a : (D * n + 1) * (142 * N ^ 2 + 1) ≤ (D + 1) * N * (143 * N ^ 2) := Nat.mul_le_mul p1 (by omega)
  have e : (D + 1) * N * (143 * N ^ 2) + N ^ 3 = (143 * (D + 1) + 1) * N ^ 3 := by ring
  omega
end Suffices

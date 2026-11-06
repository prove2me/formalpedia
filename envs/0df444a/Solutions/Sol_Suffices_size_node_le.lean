-- Prove2me | solution 1 for Suffices.size_node_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:45:52.590864+00:00
-- url     : https://prove2.me/submissions/fd41d176-d897-4467-9bc0-d75e33294351

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Suffices_Defs
import Definitions.Def_Exits_Tested
import Definitions.Def_StepMachines_Prog_Sat
import Definitions.Def_StepMachines_Prog_Sat
import Mathlib.Tactic.Ring
import Definitions.Def_Suffices_Sizes
import Theorems.Thm_Suffices_size_clauses_le
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_size_prod
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local simp] Groundwork.size_prod



set_option autoImplicit false
section
section
open Suffices
open Groundwork Groundwork.Prog CountKSat Exits
namespace Suffices
theorem _root_.solution {x : CNode} {m n N : ℕ} (h1 : x.1.length ≤ m * 2 ^ 3) (h2 : x.2.length ≤ 2 * n) (h3 : ∀ C ∈ x.1, C.length ≤ 3 ∧ ∀ l ∈ C, l.1 < n)
    (h4 : ∀ C ∈ x.2, C.length ≤ 2 ∧ ∀ l ∈ C, l.1 < n) (hm : m ≤ N) (hn : n ≤ N) (hN : 1 ≤ N) : size x ≤ 142 * N ^ 2 := by
  have s1 := size_clauses_le h1 h3 le_rfl hn hN
  have s2 := size_clauses_le h2 h4 (by omega) hn hN
  have a1 : m * 2 ^ 3 * (14 * N) ≤ 8 * N * (14 * N) := Nat.mul_le_mul_right _ (by omega)
  have a2 : 2 * n * (14 * N) ≤ 2 * N * (14 * N) := Nat.mul_le_mul_right _ (by omega)
  have e : 8 * N * (14 * N) + 2 * N * (14 * N) = 140 * N ^ 2 := by ring
  have hN2 : 1 ≤ N ^ 2 := Nat.one_le_pow _ _ hN
  rw [size_prod]
  omega
end Suffices

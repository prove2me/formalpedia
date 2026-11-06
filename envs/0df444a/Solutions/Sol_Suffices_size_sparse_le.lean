-- Prove2me | solution 1 for Suffices.size_sparse_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:46:26.453464+00:00
-- url     : https://prove2.me/submissions/e25d2547-4c8b-4459-a750-3cd4f6e6a9bb

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
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open Suffices
open Groundwork Groundwork.Prog CountKSat Exits
namespace Suffices
theorem _root_.solution {Φ : Fml} {M n N : ℕ} (hm : Φ.length ≤ M * n) (hx : ∀ C ∈ Φ, C.length ≤ 3 ∧ ∀ l ∈ C, l.1 < n) (hn : n ≤ N) (hN : 1 ≤ N) : size Φ + n ≤ (14 * M + 2) * N ^ 2 := by
  have s1 := size_clauses_le hm hx le_rfl hn hN
  have a : M * n * (14 * N) ≤ M * N * (14 * N) := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hn)
  have e : M * N * (14 * N) + 2 * N ^ 2 = (14 * M + 2) * N ^ 2 := by ring
  have hNN : N ≤ N ^ 2 := by nlinarith
  omega
end Suffices

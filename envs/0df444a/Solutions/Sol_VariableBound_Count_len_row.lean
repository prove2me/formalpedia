-- Prove2me | solution 1 for VariableBound.Count.len_row
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:42:25.855456+00:00
-- url     : https://prove2.me/submissions/b8f1e21f-de8f-4595-841a-ebde54000f45

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Count_Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_VariableBound_Count_Correct
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open VariableBound VariableBound.Count
open Groundwork Groundwork.Prog PaddedDescent.F PaddedDescent.F.Mark ClauseBound.Alg ClauseBound.ParityChecks AppVariables VariableBound.Net Finset
namespace VariableBound.Count
theorem _root_.solution (N : ℕ) (l : List ℕ) (h : ∀ E ∈ l, E ≤ N) : len l ≤ l.length * (3 * Nat.size N + 4) + 2 := by
  induction l with
  | nil => rw [len_nil]; omega
  | cons a t ih =>
    have h1 := ih fun E hE => h E (List.mem_cons_of_mem _ hE)
    have h2 := Nat.size_le_size (h a List.mem_cons_self)
    rw [len_cons, len_nat, List.length_cons, add_mul, one_mul]
    omega
end VariableBound.Count

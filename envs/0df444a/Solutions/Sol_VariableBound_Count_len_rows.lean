-- Prove2me | solution 1 for VariableBound.Count.len_rows
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:37:22.312205+00:00
-- url     : https://prove2.me/submissions/01ed6eff-a499-4ebd-b67d-4a9a3b70443c

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
theorem _root_.solution (c : ℕ) (L : List (List ℕ)) (h : ∀ l ∈ L, len l ≤ c) : len L ≤ L.length * (c + 2) + 2 := by
  induction L with
  | nil => rw [len_nil]; omega
  | cons a t ih =>
    have h1 := ih fun l hl => h l (List.mem_cons_of_mem _ hl)
    have h2 := h a List.mem_cons_self
    rw [len_cons, List.length_cons, add_mul, one_mul]
    omega
end VariableBound.Count

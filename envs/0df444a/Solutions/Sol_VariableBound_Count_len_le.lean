-- Prove2me | solution 1 for VariableBound.Count.len_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:49:06.398255+00:00
-- url     : https://prove2.me/submissions/695075ec-a848-4e3c-8a2a-4d928dec6803

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Count_Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_VariableBound_Count_Correct
import Theorems.Thm_VariableBound_Count_len_row
import Theorems.Thm_VariableBound_Count_len_rows
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_TM_Run_trans
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open VariableBound VariableBound.Count
open Groundwork Groundwork.Prog PaddedDescent.F PaddedDescent.F.Mark ClauseBound.Alg ClauseBound.ParityChecks AppVariables VariableBound.Net Finset
namespace VariableBound.Count
theorem _root_.solution (R s N : ℕ) (L : List (List ℕ)) (h1 : L.length ≤ R) (h2 : ∀ l ∈ L, l.length ≤ s ∧ ∀ E ∈ l, E ≤ N) :
    len L ≤ 8 * (R + 1) * (s + 1) * (Nat.size N + 2) + 8 := by
  have h3 : ∀ l ∈ L, len l ≤ s * (3 * Nat.size N + 4) + 2 := fun l hl =>
    (len_row N l (h2 l hl).2).trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ (h2 l hl).1) _)
  have h4 := len_rows _ L h3
  have h5 : L.length * (s * (3 * Nat.size N + 4) + 2 + 2) ≤ R * (s * (3 * Nat.size N + 4) + 2 + 2) := Nat.mul_le_mul_right _ h1
  generalize Nat.size N = z at *
  nlinarith [Nat.zero_le (R * s * z), Nat.zero_le (R * s), Nat.zero_le (R * z), Nat.zero_le (s * z), Nat.zero_le R, Nat.zero_le s, Nat.zero_le z]
end VariableBound.Count

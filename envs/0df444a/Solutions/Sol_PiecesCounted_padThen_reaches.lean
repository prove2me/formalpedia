-- Prove2me | solution 1 for PiecesCounted.padThen_reaches
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:01:33.755211+00:00
-- url     : https://prove2.me/submissions/68b15acd-b35c-456b-b49f-a04416c082b1

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PiecesCountedStatement
import Definitions.Def_ToTuring_Poly_Comb
import Definitions.Def_PiecesCounted_Sizes
import Mathlib.Tactic
import Definitions.Def_PiecesCounted_PadThen
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_PiecesCounted_size_units
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open PiecesCounted
open Groundwork
variable {α β : Type}
namespace PiecesCounted
theorem _root_.solution [HasSize α] [HasSize β] (N : α → ℕ) (f : α × List Unit → β) (a : α) {S : ℕ} (h1 : size a + size (N a) + (2 * N a + 1) + 1 ≤ S)
    (h2 : size (f (a, List.replicate (N a) ())) + 1 ≤ S) (k : ℕ) :
    ∀ j, j + k = N a → (padThen N f).Reaches S (f (a, List.replicate (N a) ())) (.inl (a, N a, List.replicate j ())) (k + 1) := by
  induction k with
  | zero =>
    intro j hj
    obtain rfl : j = N a := by omega
    refine .step rfl ?_ ?_
    · change size a + (size (N a) + size (List.replicate (N a) ())) + 1 ≤ S
      rw [size_units, List.length_replicate]
      omega
    · have hn : ¬ (List.replicate (N a) ()).length < N a := by rw [List.length_replicate]; omega
      have e : (padThen N f).step (.inl (a, N a, List.replicate (N a) ())) = .inr (f (a, List.replicate (N a) ())) := if_neg hn
      rw [e]
      exact .halt rfl (by change size (f (a, List.replicate (N a) ())) + 1 ≤ S; exact h2)
  | succ k ih =>
    intro j hj
    refine .step rfl ?_ ?_
    · change size a + (size (N a) + size (List.replicate j ())) + 1 ≤ S
      rw [size_units, List.length_replicate]
      omega
    · have hn : (List.replicate j ()).length < N a := by rw [List.length_replicate]; omega
      have e : (padThen N f).step (.inl (a, N a, List.replicate j ())) = .inl (a, N a, List.replicate (j + 1) ()) := if_pos hn
      rw [e]
      exact ih (j + 1) (by omega)
end PiecesCounted

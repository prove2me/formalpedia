-- Prove2me | solution 1 for PiecesCounted.padThen_runs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:10:49.794363+00:00
-- url     : https://prove2.me/submissions/ba4fa9c9-9b47-40b9-9146-eaee91823663

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PiecesCountedStatement
import Definitions.Def_ToTuring_Poly_Comb
import Definitions.Def_PiecesCounted_Sizes
import Mathlib.Tactic
import Definitions.Def_PiecesCounted_PadThen
import Theorems.Thm_PiecesCounted_padThen_reaches

set_option autoImplicit false
section
section
open PiecesCounted
open Groundwork
variable {α β : Type}
namespace PiecesCounted
theorem _root_.solution [HasSize α] [HasSize β] (N : α → ℕ) (f : α × List Unit → β) (a : α) {S : ℕ} (h1 : size a + size (N a) + (2 * N a + 1) + 1 ≤ S)
    (h2 : size (f (a, List.replicate (N a) ())) + 1 ≤ S) : (padThen N f).Runs a (N a + 1) S (f (a, List.replicate (N a) ())) :=
  padThen_reaches N f a h1 h2 (N a) 0 (by omega)
end PiecesCounted

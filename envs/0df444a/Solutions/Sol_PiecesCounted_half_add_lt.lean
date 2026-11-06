-- Prove2me | solution 1 for PiecesCounted.half_add_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:03:01.362752+00:00
-- url     : https://prove2.me/submissions/c266c1c8-a40e-4d35-96ea-75c99912243a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PiecesCountedStatement
import Definitions.Def_PiecesCounted_Padded
import Definitions.Def_PiecesCounted_PaddedData
import Definitions.Def_GeneralPieces_Main
import Definitions.Def_ToTuring_Lib_Int
import Definitions.Def_ToTuring_Lib_Unary
import Mathlib.Tactic
import Definitions.Def_PiecesCounted_Half

set_option autoImplicit false
section
section
open PiecesCounted
open Finset Groundwork Groundwork.Prog ClauseBound.Alg
namespace PiecesCounted
theorem _root_.solution {n N : ℕ} (hn : n ≤ N) (hN : 1 ≤ N) : (n - 1) / 2 + N < 2 ^ N := by
  obtain ⟨k, rfl⟩ : ∃ k, N = k + 1 := ⟨N - 1, by omega⟩
  have := Nat.lt_two_pow_self (n := k)
  rw [pow_succ]
  omega
end PiecesCounted

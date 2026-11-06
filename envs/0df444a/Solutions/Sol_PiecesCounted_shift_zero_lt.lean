-- Prove2me | solution 1 for PiecesCounted.shift_zero_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:55:21.169426+00:00
-- url     : https://prove2.me/submissions/e8ad4634-6996-47a0-ba3d-1fec9f11de8d

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PiecesCounted_Padded
import Definitions.Def_PiecesCounted_PaddedData
import Definitions.Def_PiecesCounted_Sizes
import Definitions.Def_PiecesFromEightSquares_LemPieces
import Mathlib.Tactic
import Definitions.Def_PiecesCounted_EightSquare

set_option autoImplicit false
section
section
open PiecesCounted
open Finset Groundwork Groundwork.Prog ClauseBound.Alg
namespace PiecesCounted
theorem _root_.solution (c lam : ℕ) : |(0 : ℤ)| + (2 * lam) ^ c < 2 ^ (2 * lam) ^ c := by
  have := Nat.lt_two_pow_self (n := (2 * lam) ^ c)
  rw [abs_zero, zero_add]
  exact_mod_cast this
end PiecesCounted

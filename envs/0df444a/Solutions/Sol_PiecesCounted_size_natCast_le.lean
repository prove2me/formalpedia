-- Prove2me | solution 1 for PiecesCounted.size_natCast_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:00:54.321707+00:00
-- url     : https://prove2.me/submissions/2bde17d0-1091-4f2b-b8ff-f7051471b6ec

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PiecesCounted_Basic
import Definitions.Def_GeneralPieces_DefGenPieces_Conv
import Mathlib.Tactic
import Definitions.Def_PiecesCounted_Sizes
import Theorems.Thm_Groundwork_RebalanceArith_size_le
import Theorems.Thm_Groundwork_size_int
attribute [local simp] Groundwork.size_int



set_option autoImplicit false
section
section
open PiecesCounted
open Finset Groundwork Groundwork.Prog
namespace PiecesCounted
theorem _root_.solution (n : ℕ) : size (n : ℤ) ≤ n + 1 := by
  have := Nat.size_le.2 (Nat.lt_two_pow_self (n := n))
  rw [size_int, Int.natAbs_natCast]
  omega
end PiecesCounted

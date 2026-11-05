-- Prove2me | solution 1 for PiecesCounted.room_le_of_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T02:49:07.236225+00:00
-- url     : https://prove2.me/submissions/2e8da634-2b31-498e-a17f-3e032a2cef42

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PiecesCountedStatement
import Definitions.Def_GeneralPieces_DefGenPieces_ToPure
import Mathlib.Tactic
import Definitions.Def_PiecesCounted_Basic
import Theorems.Thm_PiecesCounted_steps_le_of_le
import Theorems.Thm_PiecesCounted_pow_two_mul_le

set_option autoImplicit false
section
section
open PiecesCounted
open Finset Groundwork Groundwork.Prog ClauseBound.Alg
namespace PiecesCounted
theorem _root_.solution {c c' lam : ℕ} (hl : 1 ≤ lam) (h : c ≤ c') : room c lam ≤ room c' lam :=
  Nat.mul_le_mul (Nat.add_le_add_right (Nat.add_le_add (steps_le_of_le lam h) (pow_two_mul_le hl h)) 8) (Nat.add_le_add_right (pow_two_mul_le hl h) 8)
end PiecesCounted

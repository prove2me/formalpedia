-- Prove2me | solution 1 for PiecesCounted.room_le_of_length_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:07:56.054007+00:00
-- url     : https://prove2.me/submissions/0b3f3ff2-2b36-4043-9b69-6dd6e371c8ee

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PiecesCountedStatement
import Definitions.Def_GeneralPieces_DefGenPieces_ToPure
import Mathlib.Tactic
import Definitions.Def_PiecesCounted_Basic
import Theorems.Thm_PiecesCounted_steps_le_of_length_le

set_option autoImplicit false
section
section
open PiecesCounted
open Finset Groundwork Groundwork.Prog ClauseBound.Alg
namespace PiecesCounted
theorem _root_.solution (c : ℕ) {lam lam' : ℕ} (h : lam ≤ lam') : room c lam ≤ room c lam' :=
  have h1 : (2 * lam) ^ c ≤ (2 * lam') ^ c := Nat.pow_le_pow_left (by omega) c
  Nat.mul_le_mul (Nat.add_le_add_right (Nat.add_le_add (steps_le_of_length_le c h) h1) 8) (Nat.add_le_add_right h1 8)
end PiecesCounted

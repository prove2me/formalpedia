-- Prove2me | solution 1 for PiecesCounted.four_steps_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T02:53:23.928696+00:00
-- url     : https://prove2.me/submissions/8faf9b87-3cf0-4c05-90af-e87606f7c332

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PiecesCountedStatement
import Definitions.Def_PiecesCounted_Sizes
import Definitions.Def_ToTuring_Poly_Comb
import Definitions.Def_GeneralPieces_Trim_Prog
import Mathlib.Tactic
import Definitions.Def_PiecesCounted_Trimmed

set_option autoImplicit false
section
section
open PiecesCounted
open Finset Groundwork Groundwork.Prog ClauseBound.Alg
namespace PiecesCounted
theorem _root_.solution (c : ℕ) {lam : ℕ} (hl : 1 ≤ lam) : 4 * steps c lam ≤ steps (c + 2) lam := by
  have h1 : 2 ^ ((c + 2) * lam) = 2 ^ (c * lam) * 2 ^ (2 * lam) := by rw [Nat.add_mul, pow_add]
  have h2 : 2 ^ 2 ≤ 2 ^ (2 * lam) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h3 := Nat.mul_le_mul_left (2 ^ (c * lam)) h2
  unfold steps
  omega
end PiecesCounted

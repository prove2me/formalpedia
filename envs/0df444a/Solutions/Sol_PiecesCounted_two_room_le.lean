-- Prove2me | solution 1 for PiecesCounted.two_room_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:04:26.791234+00:00
-- url     : https://prove2.me/submissions/80313b0c-1126-413b-bed9-3c947fe3b18d

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PiecesCountedStatement
import Definitions.Def_PiecesCounted_Sizes
import Definitions.Def_ToTuring_Poly_Comb
import Definitions.Def_GeneralPieces_Trim_Prog
import Mathlib.Tactic
import Definitions.Def_PiecesCounted_Trimmed
import Theorems.Thm_PiecesCounted_four_steps_le
import Theorems.Thm_PiecesCounted_room_eq
import Theorems.Thm_PiecesCounted_two_mul_le_pow


set_option autoImplicit false
section
section
open PiecesCounted
open Finset Groundwork Groundwork.Prog ClauseBound.Alg
namespace PiecesCounted
theorem _root_.solution {c lam : ℕ} (hc : 1 ≤ c) (hl : 1 ≤ lam) : 2 * room c lam + 3 ≤ room (c + 2) lam := by
  have h1 : 4 * 2 ^ (c * lam) ≤ 2 ^ ((c + 2) * lam) := four_steps_le c hl
  have h2 : 4 * (2 * lam) ^ c ≤ (2 * lam) ^ (c + 2) := by
    have e : (2 * lam) ^ (c + 2) = (2 * lam) ^ c * (2 * lam) ^ 2 := pow_add _ _ _
    have e2 : 2 ^ 2 ≤ (2 * lam) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have := Nat.mul_le_mul_left ((2 * lam) ^ c) e2
    omega
  have h3 : (4 * 2 ^ (c * lam) + 4 * (2 * lam) ^ c + 8) * (4 * (2 * lam) ^ c + 8) ≤ room (c + 2) lam :=
    Nat.mul_le_mul (by omega) (by omega)
  have h4 : (4 * 2 ^ (c * lam) + 4 * (2 * lam) ^ c + 8) * (4 * (2 * lam) ^ c + 8) =
      16 * (2 ^ (c * lam) * (2 * lam) ^ c) + 32 * 2 ^ (c * lam) + 16 * ((2 * lam) ^ c * (2 * lam) ^ c) + 64 * (2 * lam) ^ c + 64 := by ring
  have h5 := room_eq c lam
  have h6 := two_mul_le_pow hc lam
  have h7 : 1 ≤ 2 ^ (c * lam) := Nat.one_le_two_pow
  omega
end PiecesCounted

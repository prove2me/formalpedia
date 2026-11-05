-- Prove2me | solution 1 for PiecesCounted.pow_two_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T02:44:52.032722+00:00
-- url     : https://prove2.me/submissions/f749658f-4a8b-47f0-86d2-34d3ed1e75ed

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PiecesCountedStatement
import Definitions.Def_GeneralPieces_DefGenPieces_ToPure
import Mathlib.Tactic
import Definitions.Def_PiecesCounted_Basic

set_option autoImplicit false
section
section
open PiecesCounted
open Finset Groundwork Groundwork.Prog ClauseBound.Alg
namespace PiecesCounted
theorem _root_.solution {c c' lam : ℕ} (hl : 1 ≤ lam) (h : c ≤ c') : (2 * lam) ^ c ≤ (2 * lam) ^ c' :=
  Nat.pow_le_pow_right (by omega) h
end PiecesCounted

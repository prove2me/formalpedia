-- Prove2me | solution 1 for PiecesCounted.trimmed_fn_of_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T02:50:36.399536+00:00
-- url     : https://prove2.me/submissions/b4e55248-367b-4eb7-afaa-00a9d31a4d5a

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
theorem _root_.solution {D : Data} {lam : ℕ} {tr : Bool} {i : ℤ} (hc : D.cap lam tr i ≤ 2 * lam) (side : Bool) (z : Pieces.Bits lam × Pieces.Bits lam) (θ : List Bool) :
    (trimmed D).fn lam tr side i z θ = D.fn lam tr side i z θ := if_pos hc
end PiecesCounted

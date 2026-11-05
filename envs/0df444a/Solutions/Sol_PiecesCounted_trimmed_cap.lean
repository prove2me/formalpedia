-- Prove2me | solution 1 for PiecesCounted.trimmed_cap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T01:05:18.267694+00:00
-- url     : https://prove2.me/submissions/b68df3b4-a641-41b4-ad14-7f233ab149c9

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
theorem _root_.solution (D : Data) (lam : ℕ) (tr : Bool) (i : ℤ) : (trimmed D).cap lam tr i = min (D.cap lam tr i) (2 * lam) := by cases tr <;> rfl
end PiecesCounted

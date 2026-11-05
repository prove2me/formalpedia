-- Prove2me | solution 1 for PiecesCounted.trimmed_fn_col
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T02:52:09.408888+00:00
-- url     : https://prove2.me/submissions/c66c86a3-67df-4ab2-b531-ed286e880ba6

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PiecesCountedStatement
import Definitions.Def_PiecesCounted_Sizes
import Definitions.Def_ToTuring_Poly_Comb
import Definitions.Def_GeneralPieces_Trim_Prog
import Mathlib.Tactic
import Definitions.Def_PiecesCounted_Trimmed
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
open PiecesCounted
open Finset Groundwork Groundwork.Prog ClauseBound.Alg
namespace PiecesCounted
theorem _root_.solution {D : Data} {lam : ℕ} {i : ℤ} (hc : ¬ D.cap lam true i ≤ 2 * lam) (z : Pieces.Bits lam × Pieces.Bits lam) (θ : List Bool) :
    (trimmed D).fn lam true true i z θ = (D.fam lam).A i (toBits lam (θ.take lam)) z.1 (toBits lam (θ.drop lam)) z.2 := ((if_neg hc).trans (if_pos rfl)).trans (if_pos rfl)
end PiecesCounted

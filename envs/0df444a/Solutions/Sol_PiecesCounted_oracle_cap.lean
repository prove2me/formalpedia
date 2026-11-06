-- Prove2me | solution 1 for PiecesCounted.oracle_cap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:04:14.687921+00:00
-- url     : https://prove2.me/submissions/018ff827-aa3d-4df4-9312-22db132e16fa

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PiecesCountedStatement
import Definitions.Def_PiecesCounted_Sizes
import Definitions.Def_ToTuring_Poly_Comb
import Definitions.Def_GeneralPieces_Trim_Prog
import Mathlib.Tactic
import Definitions.Def_PiecesCounted_Trimmed
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_TM_Run_trans
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open PiecesCounted
open Finset Groundwork Groundwork.Prog ClauseBound.Alg
namespace PiecesCounted
theorem _root_.solution {D : Data} {u : List Unit} (hl : 1 ≤ u.length) {i : ℤ} (hi : i ∈ (D.fam u.length).I) (tr : Bool) :
    D.oracle (u, .inr (.inr (.inl (tr, i)))) = some (.inl (D.cap u.length tr i)) := (if_pos hl).trans (if_pos hi)
end PiecesCounted

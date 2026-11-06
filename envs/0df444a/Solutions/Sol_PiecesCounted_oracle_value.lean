-- Prove2me | solution 1 for PiecesCounted.oracle_value
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:04:18.04602+00:00
-- url     : https://prove2.me/submissions/f95ff026-a5fd-411d-a3b5-3db2196a3f14

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
theorem _root_.solution {D : Data} {u : List Unit} (hl : 1 ≤ u.length) {i : ℤ} (hi : i ∈ (D.fam u.length).I) {l1 l2 l3 l4 : List Bool} (e1 : l1.length = u.length) (e2 : l2.length = u.length)
    (e3 : l3.length = u.length) (e4 : l4.length = u.length) :
    D.oracle (u, .inr (.inr (.inr (.inl (i, l1, l2, l3, l4))))) = some (.inl ((D.fam u.length).A i (toBits _ l1) (toBits _ l2) (toBits _ l3) (toBits _ l4))) :=
  (if_pos hl).trans (if_pos ⟨hi, e1, e2, e3, e4⟩)
end PiecesCounted

-- Prove2me | solution 1 for PiecesCounted.oracle_fn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:04:22.162249+00:00
-- url     : https://prove2.me/submissions/556ea8b7-5823-48af-9737-192a51e525a3

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
theorem _root_.solution {D : Data} {u : List Unit} (hl : 1 ≤ u.length) {i : ℤ} (hi : i ∈ (D.fam u.length).I) {tr : Bool} (side : Bool) {l1 l2 θ : List Bool} (e1 : l1.length = u.length)
    (e2 : l2.length = u.length) (e3 : θ.length = D.cap u.length tr i) :
    D.oracle (u, .inr (.inr (.inr (.inr ((tr, side), i, l1, l2, θ))))) = some (.inl (D.fn u.length tr side i (toBits _ l1, toBits _ l2) θ)) :=
  (if_pos hl).trans (if_pos ⟨hi, e1, e2, e3⟩)
end PiecesCounted

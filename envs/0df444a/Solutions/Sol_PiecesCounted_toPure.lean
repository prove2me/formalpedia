-- Prove2me | solution 1 for PiecesCounted.toPure
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:00:00.152397+00:00
-- url     : https://prove2.me/submissions/c075e0ce-0469-46ba-bcf5-c3fcea4f680d

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PiecesCountedStatement
import Definitions.Def_GeneralPieces_DefGenPieces_ToPure
import Mathlib.Tactic
import Definitions.Def_PiecesCounted_Basic
import Theorems.Thm_GeneralPieces_DefGenPieces_sum_bitsOf
import Theorems.Thm_GeneralPieces_Trim_length_bitsOf
import Theorems.Thm_Groundwork_PolyT_sum
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_Groundwork_mem_words
attribute [local fun_prop] Groundwork.PolyT.sum
attribute [local simp] GeneralPieces.Trim.length_bitsOf
attribute [local simp] Groundwork.mem_words



set_option autoImplicit false
section
section
open PiecesCounted
open Finset Groundwork Groundwork.Prog ClauseBound.Alg
namespace PiecesCounted
theorem _root_.solution : ToPure := fun D _ _ h lam hl =>
  { d_pos := h.d_pos lam hl
    sum_eq := h.sum lam hl
    row := fun i hi => ⟨fun z θ => D.fn lam false false i z (bitsOf θ), fun z θ => D.fn lam false true i z (bitsOf θ),
      fun z z' => (h.row lam hl i hi z.1 z.2 z'.1 z'.2).trans (GeneralPieces.DefGenPieces.sum_bitsOf (n := (D.fam lam).crow i) fun θ => D.fn lam false false i z θ * D.fn lam false true i z' θ).symm,
      fun z θ => h.size_f lam hl i hi false false z _ (mem_words.2 (GeneralPieces.Trim.length_bitsOf θ)),
      fun z θ => h.size_f lam hl i hi false true z _ (mem_words.2 (GeneralPieces.Trim.length_bitsOf θ))⟩
    col := fun i hi => ⟨fun z θ => D.fn lam true false i z (bitsOf θ), fun z θ => D.fn lam true true i z (bitsOf θ),
      fun z z' => (h.col lam hl i hi z.1 z'.1 z.2 z'.2).trans (GeneralPieces.DefGenPieces.sum_bitsOf (n := (D.fam lam).ccol i) fun θ => D.fn lam true false i z θ * D.fn lam true true i z' θ).symm,
      fun z θ => h.size_f lam hl i hi true false z _ (mem_words.2 (GeneralPieces.Trim.length_bitsOf θ)),
      fun z θ => h.size_f lam hl i hi true true z _ (mem_words.2 (GeneralPieces.Trim.length_bitsOf θ))⟩
    caps := h.caps lam hl
    card_I := h.card lam hl
    abs_d := h.size_d lam hl
    abs_I := h.size_I lam hl
    abs_A := h.size_A lam hl }
end PiecesCounted

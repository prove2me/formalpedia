-- Prove2me | solution 1 for PiecesCounted.answerOf_polyT
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:11:01.977962+00:00
-- url     : https://prove2.me/submissions/6825e077-9d34-4062-bc5f-d0d38e941578

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PiecesCounted_PadThen
import Definitions.Def_PiecesCounted_PaddedData
import Definitions.Def_PiecesCounted_Sizes
import Definitions.Def_ToTuring_Lib_Int
import Definitions.Def_ToTuring_Lib_Unary
import Mathlib.Tactic
import Definitions.Def_PiecesCounted_Padded
import Theorems.Thm_PiecesCounted_answer_polyT
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_Unary_poly
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open PiecesCounted
open Finset Groundwork Groundwork.Prog ClauseBound.Alg
namespace PiecesCounted
theorem _root_.solution {ρ : ℝ} {c : ℕ} {P : PiecesF} {A : (lam : ℕ) → ℕ → Pieces.Four lam} {val : AppRunningTime.ValQ → ℤ} {shift : ℕ → ℤ} (h : AppRunningTime.IsPieces ρ c P A val)
    (hs : PolyT fun u : List Unit => shift u.length) : PolyT (answerOf P val shift) :=
  answer_polyT (dF := fun u => P.d 0 u.length) (rg := fun u => List.range (P.cnt 0 u.length)) (capF := fun p => P.cap p.1 0 p.2.1.length p.2.2) (sh := fun u => shift u.length)
    h.time_d (PolyT.range h.time_cnt) h.time_cap.poly hs h.time_top h.time_bot h.time_val
end PiecesCounted

-- Prove2me | solution 1 for PiecesCounted.algOf_polyT
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:19:00.290895+00:00
-- url     : https://prove2.me/submissions/87222288-8bbc-4fd8-b7a4-82d1d5ff2808

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
import Theorems.Thm_PiecesCounted_answerOf_polyT
import Theorems.Thm_PiecesCounted_two_pow_polyT
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open PiecesCounted
open Finset Groundwork Groundwork.Prog ClauseBound.Alg
namespace PiecesCounted
theorem _root_.solution {ρ : ℝ} {c : ℕ} {P : PiecesF} {A : (lam : ℕ) → ℕ → Pieces.Four lam} {val : AppRunningTime.ValQ → ℤ} {shift : ℕ → ℤ} (h : AppRunningTime.IsPieces ρ c P A val)
    (hs : PolyT fun u : List Unit => shift u.length) (k : ℕ) : Nonempty (IsPolyT (algOf P val k shift)) :=
  ⟨padThenIsPolyT (two_pow_polyT k) (answerOf_polyT h hs)⟩
end PiecesCounted

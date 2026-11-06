-- Prove2me | solution 1 for PiecesCounted.toBits_drop
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:03:19.737843+00:00
-- url     : https://prove2.me/submissions/2fbc24c8-a370-4d60-923b-32ccc5c2d17d

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PiecesCountedStatement
import Definitions.Def_PiecesCounted_Sizes
import Definitions.Def_ToTuring_Poly_Comb
import Definitions.Def_GeneralPieces_Trim_Prog
import Mathlib.Tactic
import Definitions.Def_PiecesCounted_Trimmed
import Theorems.Thm_PiecesCounted_toBits_bitsOf
import Theorems.Thm_GeneralPieces_Trim_length_bitsOf
attribute [local simp] GeneralPieces.Trim.length_bitsOf



set_option autoImplicit false
section
section
open PiecesCounted
open Finset Groundwork Groundwork.Prog ClauseBound.Alg
namespace PiecesCounted
theorem _root_.solution {n : ℕ} (x y : Pieces.Bits n) : toBits n ((bitsOf x ++ bitsOf y).drop n) = y := by
  rw [List.drop_left' (GeneralPieces.Trim.length_bitsOf x), toBits_bitsOf]
end PiecesCounted

-- Prove2me | solution 1 for PiecesCounted.halfPiecesExist
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:58:39.642459+00:00
-- url     : https://prove2.me/submissions/c6380f2a-aaca-4398-9626-7e268e8cb83a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PiecesCountedStatement
import Definitions.Def_PiecesCounted_Padded
import Definitions.Def_PiecesCounted_PaddedData
import Definitions.Def_GeneralPieces_Main
import Definitions.Def_ToTuring_Lib_Int
import Definitions.Def_ToTuring_Lib_Unary
import Mathlib.Tactic
import Definitions.Def_PiecesCounted_Half
import Theorems.Thm_PiecesCounted_halfPieces

set_option autoImplicit false
section
section
open PiecesCounted
open Finset Groundwork Groundwork.Prog ClauseBound.Alg
namespace PiecesCounted
theorem _root_.solution : HalfPiecesExist :=
  let ⟨c, D, Alg, h, _⟩ := halfPieces
  ⟨c, D, Alg, h⟩
end PiecesCounted

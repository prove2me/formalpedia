-- Prove2me | solution 1 for PiecesCounted.halfPieces
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:44:10.529072+00:00
-- url     : https://prove2.me/submissions/aea8c5f5-0e7c-4824-964b-a91cc4ec873c

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
import Theorems.Thm_PiecesCounted_halfPiecesFrom
import Theorems.Thm_AppRunningTime_thmHalfPieces
import Theorems.Thm_GeneralPieces_thmHalfPieces
import Theorems.Thm_PiecesCounted_fromPadded


set_option autoImplicit false
section
section
open PiecesCounted
open Finset Groundwork Groundwork.Prog ClauseBound.Alg
namespace PiecesCounted
theorem _root_.solution : HalfPieces := halfPiecesFrom AppRunningTime.thmHalfPieces fromPadded
end PiecesCounted

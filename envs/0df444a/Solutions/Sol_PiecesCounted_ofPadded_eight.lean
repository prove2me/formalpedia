-- Prove2me | solution 1 for PiecesCounted.ofPadded_eight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:13:31.764055+00:00
-- url     : https://prove2.me/submissions/2f646bc2-dbc3-4e6b-b9e0-1641d63b3a8f

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PiecesCounted_Padded
import Definitions.Def_PiecesCounted_PaddedData
import Definitions.Def_PiecesCounted_Sizes
import Definitions.Def_PiecesFromEightSquares_LemPieces
import Mathlib.Tactic
import Definitions.Def_PiecesCounted_EightSquare

set_option autoImplicit false
section
section
open PiecesCounted
open Finset Groundwork Groundwork.Prog ClauseBound.Alg
namespace PiecesCounted
theorem _root_.solution (c : ℕ) : ofPadded Eight.eightF Eight.A c (fun _ => 0) = ofPadded Eight.eightF Eight.A 0 fun _ => 0 := rfl
end PiecesCounted

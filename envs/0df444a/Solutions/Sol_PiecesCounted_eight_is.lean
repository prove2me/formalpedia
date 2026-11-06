-- Prove2me | solution 1 for PiecesCounted.eight_is
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:35:56.430942+00:00
-- url     : https://prove2.me/submissions/e71a01ff-3a41-419d-ae7b-08b56292f662

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PiecesCounted_Padded
import Definitions.Def_PiecesCounted_PaddedData
import Definitions.Def_PiecesCounted_Sizes
import Definitions.Def_PiecesFromEightSquares_LemPieces
import Mathlib.Tactic
import Definitions.Def_PiecesCounted_EightSquare
import Theorems.Thm_PiecesCounted_ofPadded_eight
import Theorems.Thm_PiecesCounted_shift_zero_lt
import Theorems.Thm_AppRunningTime_lemPiecesPieces
import Theorems.Thm_PiecesCounted_ofPadded_is


set_option autoImplicit false
section
section
open PiecesCounted
open Finset Groundwork Groundwork.Prog ClauseBound.Alg
namespace PiecesCounted
theorem _root_.solution {c : ℕ} (hc : 8 ≤ c) : (ofPadded Eight.eightF Eight.A 0 fun _ => 0).Is (11 / 12) c :=
  ofPadded_eight c ▸ ofPadded_is (AppRunningTime.lemPiecesPieces c hc).1 fun lam _ => shift_zero_lt c lam
end PiecesCounted

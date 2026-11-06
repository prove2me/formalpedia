-- Prove2me | solution 1 for PiecesCounted.eight_computes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:41:27.118342+00:00
-- url     : https://prove2.me/submissions/f82542d8-e4cd-4286-a3c6-1f90efcf1975

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PiecesCounted_Padded
import Definitions.Def_PiecesCounted_PaddedData
import Definitions.Def_PiecesCounted_Sizes
import Definitions.Def_PiecesFromEightSquares_LemPieces
import Mathlib.Tactic
import Definitions.Def_PiecesCounted_EightSquare
import Theorems.Thm_PiecesCounted_answerOf_eight
import Theorems.Thm_PiecesCounted_eight_is
import Theorems.Thm_AppRunningTime_lemPiecesPieces
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_PiecesCounted_answerOf_eq
import Theorems.Thm_PiecesCounted_computes_of_answer


set_option autoImplicit false
section
section
open PiecesCounted
open Finset Groundwork Groundwork.Prog ClauseBound.Alg
namespace PiecesCounted
theorem _root_.solution {c : ℕ} (hc : 8 ≤ c) : Computes (algOf Eight.eightF AppRunningTime.valEight 0 fun _ => 0) (ofPadded Eight.eightF Eight.A 0 fun _ => 0) c :=
  computes_of_answer (eight_is hc) (Nat.zero_le c) le_rfl (by omega) fun g _ hg =>
    (answerOf_eight g _ _).trans (answerOf_eq (c := c) (shift := fun _ => 0) (AppRunningTime.lemPiecesPieces c hc).1 hg)
end PiecesCounted

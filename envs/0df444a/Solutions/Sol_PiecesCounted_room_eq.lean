-- Prove2me | solution 1 for PiecesCounted.room_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T01:03:51.166542+00:00
-- url     : https://prove2.me/submissions/d63b6bf4-5450-406f-841b-f5b08b0337d2

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PiecesCounted_Basic
import Definitions.Def_GeneralPieces_DefGenPieces_Conv
import Mathlib.Tactic
import Definitions.Def_PiecesCounted_Sizes

set_option autoImplicit false
section
section
open PiecesCounted
open Finset Groundwork Groundwork.Prog
namespace PiecesCounted
theorem _root_.solution (c lam : ℕ) : room c lam = 2 ^ (c * lam) * (2 * lam) ^ c + 8 * 2 ^ (c * lam) + (2 * lam) ^ c * (2 * lam) ^ c + 16 * (2 * lam) ^ c + 64 := by
  unfold room
  ring
end PiecesCounted

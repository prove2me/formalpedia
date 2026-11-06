-- Prove2me | solution 1 for PiecesCounted.steps_le_of_length_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:59:57.535435+00:00
-- url     : https://prove2.me/submissions/5e210089-6320-4309-8069-35434d0022cb

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PiecesCountedStatement
import Definitions.Def_GeneralPieces_DefGenPieces_ToPure
import Mathlib.Tactic
import Definitions.Def_PiecesCounted_Basic

set_option autoImplicit false
section
section
open PiecesCounted
open Finset Groundwork Groundwork.Prog ClauseBound.Alg
namespace PiecesCounted
theorem _root_.solution (c : ℕ) {lam lam' : ℕ} (h : lam ≤ lam') : steps c lam ≤ steps c lam' :=
  Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ h)
end PiecesCounted

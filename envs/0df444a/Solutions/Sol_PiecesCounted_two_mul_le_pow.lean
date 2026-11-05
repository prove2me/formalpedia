-- Prove2me | solution 1 for PiecesCounted.two_mul_le_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T01:04:07.951829+00:00
-- url     : https://prove2.me/submissions/1081c51d-a3c3-485b-a399-b43bba47ba57

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
theorem _root_.solution {c : ℕ} (hc : 1 ≤ c) (lam : ℕ) : 2 * lam ≤ (2 * lam) ^ c := Nat.le_self_pow (by omega) _
end PiecesCounted

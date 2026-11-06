-- Prove2me | solution 1 for PiecesCounted.units_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:01:53.303572+00:00
-- url     : https://prove2.me/submissions/fd833d4a-7f2a-4443-bf96-1f171c907464

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PiecesCountedStatement
import Mathlib.Tactic
import Definitions.Def_PiecesCounted_PaddedData
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open PiecesCounted
open Finset Groundwork Groundwork.Prog ClauseBound.Alg
namespace PiecesCounted
theorem _root_.solution (u : List Unit) : List.replicate u.length () = u := (List.eq_replicate_iff.2 ⟨rfl, fun _ _ => rfl⟩).symm
end PiecesCounted

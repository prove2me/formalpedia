-- Prove2me | solution 1 for PiecesCounted.fromPadded
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:35:33.627821+00:00
-- url     : https://prove2.me/submissions/1ce7358c-112d-4cd1-ac2b-0ecde420a759

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PiecesCounted_PadThen
import Definitions.Def_PiecesCounted_PaddedData
import Definitions.Def_PiecesCounted_Sizes
import Definitions.Def_ToTuring_Lib_Int
import Definitions.Def_ToTuring_Lib_Unary
import Mathlib.Tactic
import Definitions.Def_PiecesCounted_Padded
import Theorems.Thm_PiecesCounted_answerOf_eq
import Theorems.Thm_PiecesCounted_algOf_polyT
import Theorems.Thm_PiecesCounted_computes_of_answer
import Theorems.Thm_PiecesCounted_Computes_grow
import Theorems.Thm_PiecesCounted_Data_Is_grow
import Theorems.Thm_PiecesCounted_ofPadded_is


set_option autoImplicit false
section
section
open PiecesCounted
open Finset Groundwork Groundwork.Prog ClauseBound.Alg
namespace PiecesCounted
theorem _root_.solution : FromPadded := fun _ c P _ val shift h hsh hs =>
  ⟨c + 1, algOf P val c shift, Nat.le_succ c, (ofPadded_is h hs).grow le_rfl h.rho_lt (Nat.le_succ c), algOf_polyT h hsh c,
    computes_of_answer (ofPadded_is h hs) le_rfl (Nat.le_succ c) le_rfl fun _ _ hg => answerOf_eq h hg⟩
end PiecesCounted

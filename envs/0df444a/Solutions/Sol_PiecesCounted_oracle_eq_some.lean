-- Prove2me | solution 1 for PiecesCounted.oracle_eq_some
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T00:03:31.971993+00:00
-- url     : https://prove2.me/submissions/53f3ee15-dcac-41ad-be5e-8f8ebb86ff5c

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PiecesCountedStatement
import Definitions.Def_GeneralPieces_DefGenPieces_ToPure
import Mathlib.Tactic
import Definitions.Def_PiecesCounted_Basic
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open PiecesCounted
open Finset Groundwork Groundwork.Prog ClauseBound.Alg
namespace PiecesCounted
theorem _root_.solution {D : Data} {g : List Unit × Question} {a : Answer} (h : D.oracle g = some a) : 1 ≤ g.1.length ∧ D.answer g.1.length g.2 = some a := by
  unfold Data.oracle at h
  split at h
  · exact ⟨‹_›, h⟩
  · cases h
end PiecesCounted

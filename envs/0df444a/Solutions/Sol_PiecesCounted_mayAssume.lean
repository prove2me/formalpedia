-- Prove2me | solution 1 for PiecesCounted.mayAssume
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:33:32.543506+00:00
-- url     : https://prove2.me/submissions/d70f491d-62d9-4e3c-ae0b-b3a0f923274c

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PiecesCounted_Trimmed
import Definitions.Def_PiecesCounted_PaddedData
import Definitions.Def_PiecesCounted_Sizes
import Mathlib.Tactic
import Definitions.Def_PiecesCounted_Assume
import Theorems.Thm_PiecesCounted_assume_computes
import Theorems.Thm_PiecesCounted_Computes_grow
import Theorems.Thm_PiecesCounted_Data_Is_grow
import Theorems.Thm_PiecesCounted_assumeAlg_polyT
import Theorems.Thm_PiecesCounted_trimmed_cap
import Theorems.Thm_PiecesCounted_trimmed_is


set_option autoImplicit false
section
section
open PiecesCounted
open Finset Groundwork Groundwork.Prog ClauseBound.Alg
namespace PiecesCounted
theorem _root_.solution : MayAssume := fun _ c D Alg h =>
  ⟨trimmed D, assumeAlg Alg, ⟨(trimmed_is h.is).grow le_rfl h.is.rho_lt (Nat.le_add_right c 2), assumeAlg_polyT h.polyTimeSteps, assume_computes h.is h.computes⟩,
    fun lam => ⟨rfl, rfl, rfl, fun tr i => by rw [trimmed_cap]; exact min_le_right _ _⟩⟩
end PiecesCounted

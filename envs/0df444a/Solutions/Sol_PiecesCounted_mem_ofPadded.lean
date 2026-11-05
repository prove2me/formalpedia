-- Prove2me | solution 1 for PiecesCounted.mem_ofPadded
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T01:04:24.112133+00:00
-- url     : https://prove2.me/submissions/40b9493e-768d-4579-8139-ba3ac617eac2

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PiecesCountedStatement
import Mathlib.Tactic
import Definitions.Def_PiecesCounted_PaddedData

set_option autoImplicit false
section
section
open PiecesCounted
open Finset Groundwork Groundwork.Prog ClauseBound.Alg
namespace PiecesCounted
theorem _root_.solution {P : PiecesF} {A : (lam : ℕ) → ℕ → Pieces.Four lam} {c : ℕ} {shift : ℕ → ℤ} {lam : ℕ} {i : ℤ} (hi : i ∈ ((ofPadded P A c shift).fam lam).I) :
    ∃ j < P.cnt 0 lam, i = (j : ℤ) + shift lam := by
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hi
  exact ⟨j, Finset.mem_range.1 hj, rfl⟩
end PiecesCounted

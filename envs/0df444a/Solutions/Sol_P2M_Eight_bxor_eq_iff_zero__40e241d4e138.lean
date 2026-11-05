-- Prove2me | solution 1 for P2M_Eight_bxor_eq_iff_zero__40e241d4e138
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:48:26.832193+00:00
-- url     : https://prove2.me/submissions/f3a361a8-da72-41a3-940b-dfd7f147b297

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_EightSquareStatement
import Mathlib.Tactic
import Definitions.Def_Eight_SecCrossing_Blocks

set_option autoImplicit false
section
section
open Eight
open Finset
namespace Eight
theorem _root_.solution (x y u v : Block) : bxor x u = bxor v y ↔ bxor (bxor x y) (bxor u v) = (false, false, false) := by
  obtain ⟨x1, x2, x3⟩ := x; obtain ⟨y1, y2, y3⟩ := y; obtain ⟨u1, u2, u3⟩ := u; obtain ⟨v1, v2, v3⟩ := v
  have h : ∀ a b c d : Bool, (a ^^ c) = (d ^^ b) ↔ ((a ^^ b) ^^ (c ^^ d)) = false := by decide
  simp only [bxor, Prod.mk.injEq, h]
end Eight

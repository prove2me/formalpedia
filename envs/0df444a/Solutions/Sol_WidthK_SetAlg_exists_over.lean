-- Prove2me | solution 1 for WidthK.SetAlg.exists_over
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T20:14:50.939479+00:00
-- url     : https://prove2.me/submissions/f175795f-f2d5-4b64-ad9f-c8b66c831e73

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsifyWidthK_Interfaces
import Mathlib.Tactic.Linarith
import Definitions.Def_SparsifyWidthK_SetAlg

set_option autoImplicit false
section
section
open WidthK WidthK.SetAlg
open Finset Groundwork Groundwork.Sparsify
variable {α : Type*} [DecidableEq α]
variable {θ : ℕ → ℕ} {F : Finset (Finset α)} {j : ℕ} {H : Finset α}
namespace WidthK.SetAlg
theorem _root_.solution (hθ : ∀ i, 1 ≤ θ i) (h : Heart θ F j H) : ∃ C, C ∈ over F j H := by
  have h1 : 1 ≤ θ (j - H.card) := hθ _
  exact card_pos.1 (by have := h.2.2; omega)
end WidthK.SetAlg

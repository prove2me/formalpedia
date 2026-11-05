-- Prove2me | solution 1 for P2M_GeneralPieces_Ring_sum_win__8dc8cdd1a805
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:37:24.798287+00:00
-- url     : https://prove2.me/submissions/e1915771-8c04-4db3-9372-41038f44ea6c

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Basic
import Definitions.Def_GeneralPieces_Ring_OpFacts

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Ring
open AppHalfPieces MvPolynomial Finset
namespace GeneralPieces.Ring
theorem _root_.solution {A : Type} [AddCommMonoid A] (M : ℕ) (G : ℤ → A) :
    ∑ k ∈ ClauseBound.Boson.win M, G k = ∑ l ∈ Icc 1 M, G (-(l : ℤ)) + ∑ k ∈ Icc 1 M, G (k : ℤ) := by
  unfold ClauseBound.Boson.win
  rw [sum_union, sum_image, sum_image]
  · intro x _ y _ h; simpa using h
  · intro x _ y _ h; simpa using h
  · rw [disjoint_left]
    intro x hx hy
    obtain ⟨l, hl, rfl⟩ := mem_image.1 hx
    obtain ⟨k, hk, h⟩ := mem_image.1 hy
    have := (mem_Icc.1 hl).1
    have := (mem_Icc.1 hk).1
    omega
end GeneralPieces.Ring

-- Prove2me | solution 1 for P2M_Groundwork_Grid_row__eq_8e7f7ade64cf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:11:54.853993+00:00
-- url     : https://prove2.me/submissions/ddf0169b-d7a1-487b-a54b-ecaf9947972d

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Groundwork_Grid_Grid
import Definitions.Def_Groundwork_Grid_RowNet
import Theorems.Thm_Groundwork_Grid_prod_eq_factorised
import Theorems.Thm_Groundwork_prod_factorised


set_option autoImplicit false
section
section
open Groundwork Groundwork.Grid
open Finset
variable {ρ γ α τ : Type}
variable [Fintype ρ] [LinearOrder ρ] [Fintype γ] [LinearOrder γ] [Fintype α] [DecidableEq α]
omit [Fintype ρ] [LinearOrder ρ]
namespace Groundwork.Grid
theorem _root_.solution {G : Rect ρ γ → α → α → α → α → ℤ} {C : Rect ρ γ → Cut α τ} (h : ∀ ω, (C ω).Factors (G ω)) (t₀ : τ)
    (a b : ρ) (z z' : RowSt ρ γ α) :
    rowΨ G a b z z' = ∑ θ ∈ rowΘ C t₀ a b, rowTop C a b z θ * rowBot C a b z' θ := by
  have h' : ∀ ω x y u v, G ω x y u v = ∑ θ ∈ (C ω).lab, (C ω).top x y θ * (C ω).bot u v θ := h
  unfold rowΨ rowΘ rowTop rowBot
  rw [prod_eq_factorised]
  simp only [h']
  rw [prod_factorised _ _ t₀]
  rw [Finset.sum_product, Finset.sum_mul_sum]
  exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring
end Groundwork.Grid

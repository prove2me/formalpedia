-- Prove2me | solution 1 for P2M_Groundwork_Grid_rowNet___43280a58588e
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:13:24.10865+00:00
-- url     : https://prove2.me/submissions/c8da66f2-5e3d-469a-b49c-8c0a95698f8e

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Groundwork_Grid_Grid
import Definitions.Def_Groundwork_Grid_RowNet
import Theorems.Thm_P2M_Groundwork_Grid_row__eq_8e7f7ade64cf

set_option autoImplicit false
section
section
open Groundwork Groundwork.Grid
open Finset
variable {ρ γ α τ : Type}
variable [Fintype ρ] [LinearOrder ρ] [Fintype γ] [LinearOrder γ] [Fintype α] [DecidableEq α]
namespace Groundwork.Grid
theorem _root_.solution {G : Rect ρ γ → α → α → α → α → ℤ} {C : Rect ρ γ → Cut α τ} (h : ∀ ω, (C ω).Factors (G ω))
    (R : Inst (ρ × γ) α) (t₀ : τ) (L : ℕ) {a b : ρ} (hab : a < b) (z z' : RowSt ρ γ α) :
    (rowNet R C t₀ L).Ψ a b z z' = rowΨ G a b z z' := by
  rw [rowΨ_eq h t₀]
  simp [Network.Ψ, Network.lab, rowNet, min_eq_left hab.le, max_eq_right hab.le, hab, not_lt.2 hab.le]
end Groundwork.Grid

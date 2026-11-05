-- Prove2me | solution 1 for P2M_Groundwork_Grid_sum___swap_e6d8d32443c0
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:07:50.974144+00:00
-- url     : https://prove2.me/submissions/294408c5-117a-45ea-b61b-ed2c236e6a09

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Groundwork_Grid_RowNet
import Definitions.Def_Groundwork_Grid_Expand
import Definitions.Def_Groundwork_Grid_Size

set_option autoImplicit false
section
section
open Groundwork Groundwork.Grid
open Finset
variable {ρ γ α τ : Type}
variable [Fintype ρ] [LinearOrder ρ] [Fintype γ] [LinearOrder γ] [Fintype α] [DecidableEq α]
omit [Fintype α] [DecidableEq α]
namespace Groundwork.Grid
theorem _root_.solution (F : Rect ρ γ → ℕ) : ∑ ω ∈ Ω γ ρ, F (ω.2, ω.1) = ∑ ω ∈ Ω ρ γ, F ω := by
  refine Finset.sum_nbij' (fun ω => (ω.2, ω.1)) (fun ω => (ω.2, ω.1)) ?_ ?_ (fun _ _ => rfl) (fun _ _ => rfl)
    fun _ _ => rfl
  · intro ω hω
    simp only [Ω, mem_filter, mem_univ, true_and] at hω ⊢
    exact ⟨hω.2, hω.1⟩
  · intro ω hω
    simp only [Ω, mem_filter, mem_univ, true_and] at hω ⊢
    exact ⟨hω.2, hω.1⟩
end Groundwork.Grid

-- Prove2me | solution 1 for WidthK.SetAlg.heavy_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:21:21.034195+00:00
-- url     : https://prove2.me/submissions/239ab916-c863-44bd-ad58-8805c0dea05f

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsifyWidthK_Interfaces
import Mathlib.Tactic.Linarith
import Definitions.Def_SparsifyWidthK_SetAlg
import Theorems.Thm_P2M_WidthK_SetAlg_red_union__1cb354c1de8b
import Theorems.Thm_WidthK_SetAlg_mem_over
import Theorems.Thm_WidthK_SetAlg_mem_petals
import Theorems.Thm_WidthK_SetAlg_card_petal
import Theorems.Thm_Groundwork_PolyT_filter
attribute [local fun_prop] Groundwork.PolyT.filter



set_option autoImplicit false
section
section
open WidthK WidthK.SetAlg
open Finset Groundwork Groundwork.Sparsify
variable {α : Type*} [DecidableEq α]
variable {θ : ℕ → ℕ} {F : Finset (Finset α)} {j : ℕ} {H : Finset α}
namespace WidthK.SetAlg
theorem _root_.solution (hF : Reduced F) (h : Heart θ F j H) :
    heavy F j H = petals F j H ∪ F.filter fun C => ∀ D ∈ petals F j H, ¬ D ⊆ C := by
  rw [heavy, red_union' hF]
  · intro D hD
    obtain ⟨C, hC, rfl⟩ := mem_petals.1 hD
    obtain ⟨hCF, -, hs⟩ := mem_over.1 hC
    obtain ⟨x, hx⟩ := h.1
    refine ⟨C, hCF, Finset.ssubset_iff_subset_ne.2 ⟨sdiff_subset, fun e => ?_⟩⟩
    have : x ∈ C \ H := by rw [e]; exact hs hx
    exact (mem_sdiff.1 this).2 hx
  · intro D hD E hE hDE
    exact eq_of_subset_of_card_le hDE (by rw [card_petal hD, card_petal hE])
end WidthK.SetAlg

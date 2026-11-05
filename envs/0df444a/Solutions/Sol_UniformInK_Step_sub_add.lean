-- Prove2me | solution 1 for UniformInK.Step.sub_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T20:19:55.713387+00:00
-- url     : https://prove2.me/submissions/19a7098a-be29-4349-b9a6-b2cb32362eb7

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_UniformInK_Spars_Defs
import Definitions.Def_SparsifyWidthK_Step
import Definitions.Def_SparsifyWidthK_Step
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic.SplitIfs
import Definitions.Def_UniformInK_Spars_Step
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_Sparsify_red_subset
import Theorems.Thm_Groundwork_TM_Run_trans
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
section
open UniformInK
open Finset Groundwork Groundwork.Sparsify WidthK
open UniformInK.Step
variable {α : Type*} [DecidableEq α]
variable {θ : ℕ → ℕ} {k j : ℕ} {F : Finset (Finset α)} {H : Finset α}
variable {τ p t : ℕ} {φ : Finset (Finset α)}
namespace UniformInK.Step
theorem _root_.solution {A : Finset (Finset α)} {r : ℕ} (h : ∀ C ∈ F, ∃ C' ∈ φ, C ⊆ C' ∧ (C'.Nonempty → C.Nonempty)) (hA : AddU θ F A r) :
    ∀ C ∈ Sparsify.red (F ∪ A), ∃ C' ∈ φ, C ⊆ C' ∧ (C'.Nonempty → C.Nonempty) := by
  intro C hC
  rcases mem_union.1 (red_subset _ hC) with hC | hC
  · exact h C hC
  · obtain ⟨C₁, hC₁, hCC₁⟩ := hA.ssub C hC
    obtain ⟨C', hC', hsub, -⟩ := h C₁ hC₁
    exact ⟨C', hC', hCC₁.subset.trans hsub, fun _ => by rw [← card_pos, hA.size C hC]; exact hA.pos⟩
end UniformInK.Step

-- Prove2me | solution 1 for WidthK.Step.sub_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:38:12.282083+00:00
-- url     : https://prove2.me/submissions/db28ed1d-93ec-4efb-930b-5f0cc05f6d80

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsifyWidthK_Interfaces
import Definitions.Def_StepMachines_Math_Sparsify
import Definitions.Def_StepMachines_Math_Sparsify
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Definitions.Def_SparsifyWidthK_Step
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_Sparsify_red_subset
import Theorems.Thm_Groundwork_TM_Run_trans
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
open WidthK
open Finset Groundwork Groundwork.Sparsify
variable {α : Type*} [DecidableEq α]
open Step
variable {θ : ℕ → ℕ} {k j : ℕ} {F : Finset (Finset α)} {H : Finset α}
variable {τ p t : ℕ} {φ : Finset (Finset α)}
open WidthK.Step
namespace WidthK.Step
theorem _root_.solution {d : ℕ → ℕ} {A : Finset (Finset α)} {r : ℕ} (h : Node θ k τ φ F p t) (hA : AddK d F A r) :
    ∀ C ∈ Sparsify.red (F ∪ A), ∃ C' ∈ φ, C ⊆ C' ∧ (C'.Nonempty → C.Nonempty) := by
  intro C hC
  rcases mem_union.1 (red_subset _ hC) with hC | hC
  · exact h.1 C hC
  · obtain ⟨C₁, hC₁, hCC₁⟩ := hA.ssub C hC
    obtain ⟨C', hC', hsub, -⟩ := h.1 C₁ hC₁
    exact ⟨C', hC', hCC₁.subset.trans hsub, fun _ => by rw [← card_pos, hA.size C hC]; exact hA.pos⟩
end WidthK.Step

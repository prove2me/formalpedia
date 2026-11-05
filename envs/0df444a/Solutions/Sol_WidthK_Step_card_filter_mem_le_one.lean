-- Prove2me | solution 1 for WidthK.Step.card_filter_mem_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:38:11.129465+00:00
-- url     : https://prove2.me/submissions/57df09cc-d985-4e1b-93da-96ed56613a29

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
import Theorems.Thm_Groundwork_PolyT_filter
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.filter



set_option autoImplicit false
section
open WidthK
open Finset Groundwork Groundwork.Sparsify
variable {α : Type*} [DecidableEq α]
open Step
variable {θ : ℕ → ℕ} {k j : ℕ} {F : Finset (Finset α)} {H : Finset α}
open WidthK.Step
namespace WidthK.Step
theorem _root_.solution {G : Finset (Finset α)} (hG : ∀ C ∈ G, C.card = 1) (y : α) :
    (G.filter fun C => y ∈ C).card ≤ 1 := by
  rw [card_le_one]
  intro C hC D hD
  obtain ⟨hC, hyC⟩ := mem_filter.1 hC
  obtain ⟨hD, hyD⟩ := mem_filter.1 hD
  obtain ⟨c, rfl⟩ := card_eq_one.1 (hG C hC)
  obtain ⟨e, rfl⟩ := card_eq_one.1 (hG D hD)
  rw [mem_singleton] at hyC hyD
  rw [← hyC, ← hyD]
end WidthK.Step

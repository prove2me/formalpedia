-- Prove2me | solution 1 for WidthK.Node.light
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:22:22.784532+00:00
-- url     : https://prove2.me/submissions/ff8a6bc9-cbf6-4dbc-84d0-36951978c7e4

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
import Theorems.Thm_WidthK_Step_sum_nextA_of_lt
import Theorems.Thm_WidthK_InvK_step
import Theorems.Thm_WidthK_Rule_add_light
import Theorems.Thm_WidthK_Step_sub_add
import Theorems.Thm_WidthK_Step_nextA_zero
import Theorems.Thm_Groundwork_PolyT_all
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
namespace WidthK
namespace Node
theorem _root_.solution (hθ : ∀ i, 0 < θ i) (h : Node θ k τ φ F p t) (hB : Rule θ k F j H) :
    Node θ k τ φ (light F H) (p + 1) t := by
  have hA := hB.add_light hθ
  refine ⟨sub_add h hA, ?_⟩
  obtain ⟨-, N, a, hh, hI, ha0, hh1, hp, ht⟩ := h
  refine ⟨_, _, hh, hI.step hA, (nextA_zero a hA.pos _).trans ha0, fun r => ?_, ?_, ht⟩
  · exact (hh1 r).trans (Nat.le_add_right _ _)
  · rw [sum_nextA_of_lt a _ (lt_of_lt_of_le hB.heart.2.1 hB.le), card_singleton]
    omega
end Node
end WidthK

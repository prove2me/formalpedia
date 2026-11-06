-- Prove2me | solution 1 for UniformInK.Step.node_light
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:57:05.506701+00:00
-- url     : https://prove2.me/submissions/ad016481-a4e6-4df8-8a91-65017878a31e

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_UniformInK_Spars_Defs
import Definitions.Def_SparsifyWidthK_Step
import Definitions.Def_SparsifyWidthK_Step
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic.SplitIfs
import Definitions.Def_UniformInK_Spars_Step
import Theorems.Thm_UniformInK_Step_inv_step
import Theorems.Thm_UniformInK_Step_add_light
import Theorems.Thm_UniformInK_Step_sub_add
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_WidthK_Node_light
import Theorems.Thm_WidthK_Rule_add_light
import Theorems.Thm_WidthK_Step_nextA_zero
import Theorems.Thm_WidthK_Step_sub_add
import Theorems.Thm_WidthK_Step_sum_nextA_of_lt
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
theorem _root_.solution (hθ : ∀ i, 1 ≤ θ i) (h : NodeU θ k τ φ F p t) (hB : Rule θ k F j H) :
    NodeU θ k τ φ (light F H) (p + 1) t := by
  have hA := add_light hθ hB
  refine ⟨sub_add h.1 hA, ?_⟩
  obtain ⟨-, N, a, hh, hI, ha0, hh1, hp, ht⟩ := h
  refine ⟨_, _, hh, inv_step hI hA, (WidthK.Step.nextA_zero a hA.pos _).trans ha0, fun r => ?_, ?_, ht⟩
  · exact (hh1 r).trans (Nat.le_add_right _ _)
  · rw [WidthK.Step.sum_nextA_of_lt a _ (lt_of_lt_of_le hB.heart.2.1 hB.le), card_singleton]
    omega
end UniformInK.Step

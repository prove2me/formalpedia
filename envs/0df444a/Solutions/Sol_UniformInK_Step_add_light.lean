-- Prove2me | solution 1 for UniformInK.Step.add_light
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:42:23.365544+00:00
-- url     : https://prove2.me/submissions/d26667b1-e0cb-48f2-9885-11c64c82f1ff

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_UniformInK_Spars_Defs
import Definitions.Def_SparsifyWidthK_Step
import Definitions.Def_SparsifyWidthK_Step
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic.SplitIfs
import Definitions.Def_UniformInK_Spars_Step
import Theorems.Thm_UniformInK_Step_card_over_le
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_filter
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_WidthK_Rule_add_light
import Theorems.Thm_WidthK_Step_card_over_le
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.filter



set_option autoImplicit false
section
section
open UniformInK
open Finset Groundwork Groundwork.Sparsify WidthK
open UniformInK.Step
variable {α : Type*} [DecidableEq α]
variable {θ : ℕ → ℕ} {k j : ℕ} {F : Finset (Finset α)} {H : Finset α}
namespace UniformInK.Step
theorem _root_.solution (hθ : ∀ i, 1 ≤ θ i) (hB : Rule θ k F j H) : AddU θ F {H} H.card where
  ssub := (hB.add_light hθ).ssub
  size := (hB.add_light hθ).size
  pos := (hB.add_light hθ).pos
  deg := by
    intro Y hY hYr
    have h1 := card_over_le hθ hB hB.heart.2.1 hY hYr
    have h2 : (({H} : Finset (Finset α)).filter fun D => Y ⊆ D).card ≤ 1 :=
      (card_le_card (filter_subset _ _)).trans (card_singleton H).le
    have h3 := hθ (H.card - Y.card)
    omega
end UniformInK.Step

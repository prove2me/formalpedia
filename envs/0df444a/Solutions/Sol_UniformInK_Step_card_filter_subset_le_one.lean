-- Prove2me | solution 1 for UniformInK.Step.card_filter_subset_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T20:19:11.347513+00:00
-- url     : https://prove2.me/submissions/16bcd245-68e1-495f-946e-7b8223b7834b

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
import Theorems.Thm_Groundwork_PolyT_filter
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
theorem _root_.solution {G : Finset (Finset α)} {r : ℕ} (hG : ∀ C ∈ G, C.card = r) {Y : Finset α} (hY : Y.card = r) :
    (G.filter fun C => Y ⊆ C).card ≤ 1 := by
  rw [card_le_one]
  intro C hC D hD
  obtain ⟨hC, hYC⟩ := mem_filter.1 hC
  obtain ⟨hD, hYD⟩ := mem_filter.1 hD
  rw [← eq_of_subset_of_card_le hYC (by rw [hG C hC, hY]), ← eq_of_subset_of_card_le hYD (by rw [hG D hD, hY])]
end UniformInK.Step

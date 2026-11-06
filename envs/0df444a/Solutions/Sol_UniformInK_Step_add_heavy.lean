-- Prove2me | solution 1 for UniformInK.Step.add_heavy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:42:26.922962+00:00
-- url     : https://prove2.me/submissions/ad626178-fb6e-4a87-9eec-e3066eb84ffa

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_UniformInK_Spars_Defs
import Definitions.Def_SparsifyWidthK_Step
import Definitions.Def_SparsifyWidthK_Step
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic.SplitIfs
import Definitions.Def_UniformInK_Spars_Step
import Theorems.Thm_UniformInK_Step_card_filter_subset_le_one
import Theorems.Thm_UniformInK_Step_card_over_le
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_filter
import Theorems.Thm_Groundwork_Stepped_Reaches_mono
import Theorems.Thm_Groundwork_Stepped_Runs_mono
import Theorems.Thm_Groundwork_TM_Frag_Within_mono
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_WidthK_Rule_add_heavy
import Theorems.Thm_WidthK_Step_card_of_mem_petals
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
theorem _root_.solution (hθ : ∀ i, 1 ≤ θ i) (hB : Rule θ k F j H) : AddU θ F (petals F j H) (j - H.card) where
  ssub := (hB.add_heavy hθ).ssub
  size := (hB.add_heavy hθ).size
  pos := (hB.add_heavy hθ).pos
  deg := by
    intro Y hY hYr
    have hH := card_pos.2 hB.heart.1
    have hlt := hB.heart.2.1
    have h1 := card_over_le hθ hB (r := j - H.card) (by omega) hY hYr
    have h2 : ((petals F j H).filter fun D => Y ⊆ D).card ≤ θ (j - H.card - Y.card) := by
      rcases hYr.eq_or_lt with he | hYlt
      · exact (card_filter_subset_le_one (fun Q hQ => WidthK.Step.card_of_mem_petals hQ) he).trans (hθ _)
      · by_cases hd : Disjoint H Y
        · have hc : (H ∪ Y).card = H.card + Y.card := card_union_of_disjoint hd
          have hYpos := card_pos.2 hY
          have hlt' : (Sparsify.over F j (H ∪ Y)).card < θ (j - H.card - Y.card) := by
            by_contra hcon
            refine hB.maxH (H ∪ Y) (by omega) ⟨hB.heart.1.mono subset_union_left, by omega, ?_⟩
            rw [hc, show j - (H.card + Y.card) = j - H.card - Y.card by omega]
            exact not_lt.1 hcon
          refine le_trans (le_trans (card_le_card ?_) (card_image_le (f := fun C => C \ H))) hlt'.le
          intro Q hQ
          obtain ⟨hQ, hYQ⟩ := mem_filter.1 hQ
          obtain ⟨C, hC, rfl⟩ := mem_image.1 hQ
          obtain ⟨hCF, hcC, hHC⟩ := mem_filter.1 hC
          exact mem_image.2 ⟨C, mem_filter.2 ⟨hCF, hcC, union_subset hHC (hYQ.trans sdiff_subset)⟩, rfl⟩
        · rw [filter_eq_empty_iff.2]
          · exact Nat.zero_le _
          · intro Q hQ hYQ
            obtain ⟨C, -, rfl⟩ := mem_image.1 hQ
            obtain ⟨x, hxH, hxY⟩ := not_disjoint_iff.1 hd
            exact (mem_sdiff.1 (hYQ hxY)).2 hxH
    omega
end UniformInK.Step

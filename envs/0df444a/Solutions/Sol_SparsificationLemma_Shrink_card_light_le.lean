-- Prove2me | solution 1 for SparsificationLemma.Shrink.card_light_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:52:40.390836+00:00
-- url     : https://prove2.me/submissions/24e40f39-dd92-4af1-b33f-b23a70db9f5c

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsificationLemma_Defs
import Definitions.Def_CountKSat_ProgC
import Definitions.Def_SparsifyWidthK_SetAlg
import Definitions.Def_SparsifyWidthK_Refine
import Definitions.Def_SparsificationLemma_Shrink
import Theorems.Thm_Groundwork_PolyT_filter
import Theorems.Thm_WidthK_Node_light
import Theorems.Thm_WidthK_stLightEq
attribute [local fun_prop] Groundwork.PolyT.filter



set_option autoImplicit false
section
section
open SparsificationLemma
open Finset Groundwork Groundwork.Prog Groundwork.Sparsify WidthK WidthK.Prog WidthK.ProgMain CountKSat
open SparsificationLemma.Shrink
variable {α : Type} [DecidableEq α] {θ : ℕ → ℕ} {F : Finset (Finset α)} {j : ℕ} {H : Finset α}
namespace SparsificationLemma.Shrink
theorem _root_.solution (hθ : ∀ i, 1 ≤ θ i) (hF : Reduced F) (h : Heart θ F j H) : (light F H).card ≤ F.card := by
  rw [stLightEq _ θ F j H hθ hF h]
  obtain ⟨E, hE⟩ := card_pos.1 (lt_of_lt_of_le (hθ _) h.2.2)
  obtain ⟨hEF, -, hHE⟩ := mem_filter.1 hE
  have hsub : (F.filter fun C => ¬ H ⊆ C) ⊆ F.erase E := by
    intro C hC
    obtain ⟨hCF, hno⟩ := mem_filter.1 hC
    exact mem_erase.2 ⟨fun e => hno (e ▸ hHE), hCF⟩
  have h1 := card_union_le ({H} : Finset (Finset α)) (F.filter fun C => ¬ H ⊆ C)
  have h2 := card_le_card hsub
  have h3 := card_pos.2 ⟨E, hEF⟩
  rw [card_singleton] at h1
  rw [card_erase_of_mem hEF] at h2
  omega
end SparsificationLemma.Shrink

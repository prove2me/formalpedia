-- Prove2me | solution 1 for SparsificationLemma.Shrink.card_heavy_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:45:58.957328+00:00
-- url     : https://prove2.me/submissions/1989d12c-b444-4ace-981c-eff3b640cabc

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsificationLemma_Defs
import Definitions.Def_CountKSat_ProgC
import Definitions.Def_SparsifyWidthK_SetAlg
import Definitions.Def_SparsifyWidthK_Refine
import Definitions.Def_SparsificationLemma_Shrink
import Theorems.Thm_Groundwork_PolyT_filter
import Theorems.Thm_WidthK_Node_heavy
import Theorems.Thm_WidthK_stHeavyEq
attribute [local fun_prop] Groundwork.PolyT.filter



set_option autoImplicit false
section
section
open SparsificationLemma
open Finset Groundwork Groundwork.Prog Groundwork.Sparsify WidthK WidthK.Prog WidthK.ProgMain CountKSat
open SparsificationLemma.Shrink
variable {α : Type} [DecidableEq α] {θ : ℕ → ℕ} {F : Finset (Finset α)} {j : ℕ} {H : Finset α}
namespace SparsificationLemma.Shrink
theorem _root_.solution (hF : Reduced F) (h : Heart θ F j H) : (heavy F j H).card ≤ F.card := by
  rw [stHeavyEq _ θ F j H hF h]
  have h1 : (petals F j H).card ≤ (Sparsify.over F j H).card := card_image_le
  have h2 : (F.filter fun C => ∀ D ∈ petals F j H, ¬ D ⊆ C) ⊆ F \ Sparsify.over F j H := by
    intro C hC
    obtain ⟨hCF, hno⟩ := mem_filter.1 hC
    exact mem_sdiff.2 ⟨hCF, fun hO => hno (C \ H) (mem_image_of_mem _ hO) sdiff_subset⟩
  calc _ ≤ (petals F j H).card + (F.filter fun C => ∀ D ∈ petals F j H, ¬ D ⊆ C).card := card_union_le _ _
    _ ≤ (Sparsify.over F j H).card + (F \ Sparsify.over F j H).card := Nat.add_le_add h1 (card_le_card h2)
    _ = F.card := by rw [Nat.add_comm]; exact card_sdiff_add_card_eq_card (filter_subset _ _)
end SparsificationLemma.Shrink

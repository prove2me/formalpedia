-- Prove2me | solution 1 for WidthK.SetAlg.sat_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:21:08.21277+00:00
-- url     : https://prove2.me/submissions/f27948bc-3cfa-4d51-80d5-6f05ea04756c

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsifyWidthK_Interfaces
import Mathlib.Tactic.Linarith
import Definitions.Def_SparsifyWidthK_SetAlg
import Theorems.Thm_WidthK_SetAlg_mem_over
import Theorems.Thm_WidthK_SetAlg_mem_petals
import Theorems.Thm_Groundwork_Sparsify_sat_red


set_option autoImplicit false
section
section
open WidthK WidthK.SetAlg
open Finset Groundwork Groundwork.Sparsify
variable {α : Type*} [DecidableEq α]
variable {θ : ℕ → ℕ} {F : Finset (Finset α)} {j : ℕ} {H : Finset α}
namespace WidthK.SetAlg
theorem _root_.solution (v : α → Prop) : Sat v F ↔ Sat v (light F H) ∨ Sat v (heavy F j H) := by
  rw [light, heavy, sat_red, sat_red]
  constructor
  · intro hsat
    by_cases hH : ∃ l ∈ H, v l
    · left
      intro C hC
      rcases mem_union.1 hC with hC | hC
      · exact hsat C hC
      · rw [mem_singleton.1 hC]; exact hH
    · right
      intro D hD
      rcases mem_union.1 hD with hD | hD
      · exact hsat D hD
      · obtain ⟨C, hC, rfl⟩ := mem_petals.1 hD
        obtain ⟨l, hl, hv⟩ := hsat C (mem_over.1 hC).1
        exact ⟨l, mem_sdiff.2 ⟨hl, fun hlH => hH ⟨l, hlH, hv⟩⟩, hv⟩
  · rintro (h | h) <;> exact fun C hC => h C (mem_union_left _ hC)
end WidthK.SetAlg

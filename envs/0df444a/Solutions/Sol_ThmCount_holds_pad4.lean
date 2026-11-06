-- Prove2me | solution 1 for ThmCount.holds_pad4
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:57:24.170503+00:00
-- url     : https://prove2.me/submissions/5d77a7f4-be22-4f10-9900-ac3cb9b593b1

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThmCount_Defs
import Definitions.Def_Wrap_FrontEnd
import Definitions.Def_WidthK_Decode
import Definitions.Def_ToTuring_Poly_Decode
import Mathlib.Tactic
import Definitions.Def_ThmCount_FrontEnd
import Theorems.Thm_Wrap_mem_pad4


set_option autoImplicit false
section
section
section
open ThmCount
open Groundwork Groundwork.Decode
namespace ThmCount
theorem _root_.solution {n : ℕ} (φ : Sat3.CNF n) (b : Fin (n + 4) → Bool) :
    (∀ D ∈ Wrap.pad4 φ, ∃ l ∈ D, b l.1 = l.2) ↔ (∀ C ∈ φ, ∃ l ∈ C, b (Fin.castAdd 4 l.1) = l.2) ∧ ∀ j : Fin 4, b (Fin.natAdd n j) = true := by
  constructor
  · intro h
    refine ⟨fun C hC => ?_, fun j => ?_⟩
    · obtain ⟨l, hl, e⟩ := h _ (Wrap.mem_pad4.2 (Or.inl ⟨C, hC, rfl⟩))
      obtain ⟨l', hl', rfl⟩ := List.mem_map.1 hl
      exact ⟨l', hl', e⟩
    · obtain ⟨l, hl, e⟩ := h _ (Wrap.mem_pad4.2 (Or.inr ⟨j, rfl⟩))
      rw [List.mem_singleton] at hl
      subst hl
      exact e
  · rintro ⟨h1, h2⟩ D hD
    rcases Wrap.mem_pad4.1 hD with ⟨C, hC, rfl⟩ | ⟨j, rfl⟩
    · obtain ⟨l, hl, e⟩ := h1 C hC
      exact ⟨_, List.mem_map_of_mem hl, e⟩
    · exact ⟨_, List.mem_singleton.2 rfl, h2 j⟩
end ThmCount

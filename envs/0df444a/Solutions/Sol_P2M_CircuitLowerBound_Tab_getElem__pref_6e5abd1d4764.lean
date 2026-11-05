-- Prove2me | solution 1 for P2M_CircuitLowerBound_Tab_getElem__pref_6e5abd1d4764
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:42:40.441982+00:00
-- url     : https://prove2.me/submissions/971a246f-b22f-44d7-962f-5b1b556b09a1

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Tab_Spec
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Tab_Frame
import Theorems.Thm_Groundwork_length_toWord
import Theorems.Thm_Groundwork_mem_words
attribute [local simp] Groundwork.length_toWord
attribute [local simp] Groundwork.mem_words



set_option autoImplicit false
section
section
open CircuitLowerBound CircuitLowerBound.Tab
open ENP Turing
namespace CircuitLowerBound.Tab
theorem _root_.solution {α : Type} : ∀ L : List (Option α), (∀ i, L[i]? = some none → ∀ x, L[i + 1]? = some x → x = none) →
    ∀ q, q < L.length → (pref L)[q]? = (L[q]?).getD none
  | [], _, q, hq => by simp at hq
  | none :: L, h, q, hq => by
    have : ∀ q, q < (none :: L).length → (none :: L)[q]? = some none := by
      intro q
      induction q with
      | zero => intro _; rfl
      | succ q ih =>
        intro hq
        obtain ⟨x, hx⟩ : ∃ x, (none :: L)[q + 1]? = some x := ⟨_, List.getElem?_eq_getElem hq⟩
        rw [hx, h q (ih (by omega)) x hx]
    rw [this q hq]
    simp [pref]
  | some a :: L, h, 0, _ => by simp [pref]
  | some a :: L, h, q + 1, hq => by
    have := solution L (fun i hi x hx => h (i + 1) (by simpa using hi) x (by simpa using hx)) q (by simpa using hq)
    simpa [pref] using this
end CircuitLowerBound.Tab

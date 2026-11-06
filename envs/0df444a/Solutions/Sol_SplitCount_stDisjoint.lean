-- Prove2me | solution 1 for SplitCount.stDisjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:19:52.1602+00:00
-- url     : https://prove2.me/submissions/a3474cad-01a9-4816-8118-9683e16055c2

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SplitCount_Defs
import Mathlib.Tactic.Tauto
import Definitions.Def_SplitCount_Disjoint
import Theorems.Thm_SplitCount_pickK_petals
import Theorems.Thm_SplitCount_holds_light
import Theorems.Thm_SplitCount_holds_heavy
import Theorems.Thm_CountKSat_StepCount_pickK_petals


set_option autoImplicit false
section
section
open SplitCount
open Groundwork Groundwork.Prog Groundwork.Sparsify WidthK.Prog CountKSat Eight.Width
namespace SplitCount
theorem _root_.solution : StDisjoint := by
  intro θ k x l h hst a
  obtain ⟨⟨H, P⟩, hp, he⟩ := Option.map_eq_some_iff.1 hst
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
  have hL := holds_light a x H
  have hR := holds_heavy a x H P (pickK_petals hp)
  constructor
  · change Holds a _ ↔ Holds a _ ∨ Holds a _
    rw [hL, hR]
    constructor
    · intro hx
      by_cases hH : ∃ l ∈ H, a l.1 = l.2
      · exact Or.inl ⟨hx, hH⟩
      · exact Or.inr ⟨hx, hH⟩
    · rintro (h | h) <;> exact h.1
  · change ¬ (Holds a _ ∧ Holds a _)
    rw [hL, hR]
    rintro ⟨h1, h2⟩
    exact h2.2 h1.2
end SplitCount

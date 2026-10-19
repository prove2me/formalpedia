-- Prove2me | solution 1 for SandsSauerWoodrow.leSet_trans
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-17T11:18:25.335404+00:00
-- url     : https://prove2.me/submissions/baf0636a-1f7f-4016-8e60-8e7bb8fc5408

import Mathlib
import Definitions.Def_opg1808_colored_tournaments
import Definitions.Def_SandsSauerWoodrow_OrderOnSets

open OPG1808

universe u
open SandsSauerWoodrow

theorem solution{V : Type u} {R : V → V → Prop} (hR : Transitive R) :
    Transitive (leSet R) := by
  intro S T U hST hTU x hx
  obtain ⟨y, hy, h1⟩ := hST x hx
  obtain ⟨z, hz, h2⟩ := hTU y hy
  refine ⟨z, hz, ?_⟩
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · left
    rw [h1, h2]
  · right
    rw [h1]
    exact h2
  · right
    rw [← h2]
    exact h1
  · right
    exact hR h1 h2

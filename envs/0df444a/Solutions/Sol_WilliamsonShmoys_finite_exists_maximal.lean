-- Prove2me | solution 1 for WilliamsonShmoys.finite_exists_maximal
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T20:44:38.374432+00:00
-- url     : https://prove2.me/submissions/47d4ab1d-4aaf-40e2-a9bf-0d85aab61f2d

import Mathlib

set_option autoImplicit false

theorem solution {α : Type} [Finite α] [PartialOrder α] (P : α → Prop)
    (hP : ∃ a, P a) : ∃ a, P a ∧ ∀ b, P b → a ≤ b → b = a := by
  classical
  let s : Set α := {a | P a}
  have hs : s.Finite := Set.toFinite s
  have hne : s.Nonempty := by
    rcases hP with ⟨a, ha⟩
    exact ⟨a, ha⟩
  obtain ⟨a, ha, hmax⟩ := hs.exists_maximal hne
  refine ⟨a, ha, ?_⟩
  intro b hb hab
  exact le_antisymm (hmax hb hab) hab
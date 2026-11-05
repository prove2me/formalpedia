-- Prove2me | solution 1 for WilliamsonShmoys.bounded_progress_has_terminal_path__p2m_9fc762a8_5f43_4315_941e_21ea4c59e3e4_a2
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-04T20:23:24.100778+00:00
-- url     : https://prove2.me/submissions/a5757ef3-1dac-4693-b835-69a95e779de3

import Mathlib

set_option autoImplicit false

theorem solution {α : Type} (B : Nat) (rank : α → Nat)
    (step : α → α → Prop) (terminal : α → Prop)
    (hbound : ∀ x, rank x ≤ B)
    (hstep : ∀ x, ¬ terminal x → ∃ y, step x y ∧ rank x < rank y) :
    ∀ x, ∃ y, Relation.ReflTransGen step x y ∧ terminal y := by
  have aux : ∀ m : Nat, ∀ x : α, B - rank x = m →
      ∃ y, Relation.ReflTransGen step x y ∧ terminal y := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro x hxm
      by_cases ht : terminal x
      · exact ⟨x, Relation.ReflTransGen.refl, ht⟩
      · obtain ⟨y, hxy, hlt⟩ := hstep x ht
        have hxB : rank x ≤ B := hbound x
        have hyB : rank y ≤ B := hbound y
        have hlt' : B - rank y < m := by omega
        obtain ⟨z, hyz, htz⟩ := ih (B - rank y) hlt' y rfl
        exact ⟨z, (Relation.ReflTransGen.single hxy).trans hyz, htz⟩
  intro x
  exact aux (B - rank x) x rfl

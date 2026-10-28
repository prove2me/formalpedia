-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximizer_on_fintype
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T04:37:16.682996+00:00
-- url     : https://prove2.me/submissions/29d5b686-46d8-4d03-a31b-49b568c7a6d0

import Mathlib
set_option autoImplicit false

theorem solution
    {α β : Type} [Fintype α] [DecidableEq α] [LinearOrder β]
    (P : α → Prop) (score : α → β) (hP : ∃ a, P a) :
    ∃ a, P a ∧ ∀ b, P b → score b ≤ score a := by
  classical
  let s : Set α := {a | P a}
  have hsFinite : s.Finite := Set.toFinite s
  have hsNonempty : s.Nonempty := by
    rcases hP with ⟨a, ha⟩
    exact ⟨a, ha⟩
  obtain ⟨a, ha, hmax⟩ := Set.exists_max_image s score hsFinite hsNonempty
  change P a at ha
  refine ⟨a, ha, ?_⟩
  intro b hb
  exact hmax b (by change P b; exact hb)
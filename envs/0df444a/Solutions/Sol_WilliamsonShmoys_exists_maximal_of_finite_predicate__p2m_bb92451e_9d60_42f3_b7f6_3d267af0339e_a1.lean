-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_of_finite_predicate__p2m_bb92451e_9d60_42f3_b7f6_3d267af0339e_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T09:38:28.786223+00:00
-- url     : https://prove2.me/submissions/d996f6ca-3f02-4df7-ad60-5da3cb3e3ef3

import Mathlib
set_option autoImplicit false

theorem solution {α : Type} [Fintype α] [PartialOrder α] (P : α → Prop)
    (hP : ∃ a, P a) : ∃ a, P a ∧ ∀ b, P b → a ≤ b → b = a := by
  classical
  let s : Set α := {a | P a}
  have hs : s.Nonempty := by
    rcases hP with ⟨a, ha⟩
    exact ⟨a, ha⟩
  obtain ⟨a, ha⟩ := (Set.toFinite s).exists_maximal hs
  refine ⟨a, ha.1, ?_⟩
  intro b hb hab
  exact (ha.2 hb hab).antisymm hab
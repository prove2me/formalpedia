-- Prove2me | solution 1 for WilliamsonShmoys.exists_max_nat_on_finite_type__p2m_07123160_8e02_4c14_a3ba_8b97213ab1a9_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T01:38:06.355788+00:00
-- url     : https://prove2.me/submissions/1dff0776-fff9-48f1-87f1-f52671d1b5d3

import Mathlib
set_option autoImplicit false

theorem solution {α : Type} [Finite α] (P : α → Prop) (f : α → Nat)
    (hex : ∃ a, P a) : ∃ a, P a ∧ ∀ b, P b → f b ≤ f a := by
  classical
  letI : Fintype α := Fintype.ofFinite α
  let s : Finset α := Finset.univ.filter P
  have hs : s.Nonempty := by
    obtain ⟨a, ha⟩ := hex
    exact ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ a, ha⟩⟩
  obtain ⟨a, ha, hmax⟩ := s.exists_max_image f hs
  refine ⟨a, ?_, ?_⟩
  · have hmem : a ∈ Finset.univ.filter P := by simpa [s] using ha
    exact (Finset.mem_filter.mp hmem).2
  · intro b hb
    exact hmax b (Finset.mem_filter.mpr ⟨Finset.mem_univ b, hb⟩)
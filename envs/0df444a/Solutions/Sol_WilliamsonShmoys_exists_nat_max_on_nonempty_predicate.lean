-- Prove2me | solution 1 for WilliamsonShmoys.exists_nat_max_on_nonempty_predicate
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T05:16:46.315089+00:00
-- url     : https://prove2.me/submissions/9c7e092a-ebdb-4adc-918f-f62abf0c809f

import Mathlib

set_option autoImplicit false

theorem solution
    {α : Type} [Fintype α] (P : α → Prop) (f : α → Nat)
    (hP : ∃ a, P a) :
    ∃ a, P a ∧ ∀ b, P b → f b ≤ f a := by
  classical
  let s : Finset α := Finset.univ.filter P
  have hs : s.Nonempty := by
    rcases hP with ⟨a, ha⟩
    exact ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ a, ha⟩⟩
  obtain ⟨a, ha, hmax⟩ := Finset.exists_max_image s f hs
  refine ⟨a, (Finset.mem_filter.mp ha).2, ?_⟩
  intro b hb
  exact hmax b (Finset.mem_filter.mpr ⟨Finset.mem_univ b, hb⟩)
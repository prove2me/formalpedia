-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_element_of_finite_predicate__p2m_5205e6ef_38db_4828_a550_3d962d50da00_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:41:18.453195+00:00
-- url     : https://prove2.me/submissions/ffd392a8-414d-4357-b3ea-c1519d199aa3

import Mathlib.Data.Fintype.Basic
import Mathlib.Order.Basic
import Mathlib.Order.WellFoundedSet

set_option autoImplicit false

theorem solution
    {α : Type} [Fintype α] [PartialOrder α]
    (P : α → Prop) (hP : ∃ a, P a) :
    ∃ a, P a ∧ ∀ b, P b → a ≤ b → b ≤ a := by
  let s : Set α := {a | P a}
  have hs : s.Finite := by
    apply Set.Finite.subset Set.finite_univ
    intro a ha
    simp
  have hwf : s.WellFoundedOn (· > ·) := hs.wellFoundedOn
  have hne : s.Nonempty := by
    rcases hP with ⟨a, ha⟩
    exact ⟨a, ha⟩
  obtain ⟨a, ha⟩ := hwf.exists_maximal hne
  refine ⟨a, ?_⟩
  change P a ∧ ∀ b, P b → a ≤ b → b ≤ a at ha
  exact ha
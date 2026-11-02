-- Prove2me | solution 1 for WilliamsonShmoys.finite_predicate_maximal__p2m_93fb4221_4029_4870_92af_deed270da66d_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:52:21.04468+00:00
-- url     : https://prove2.me/submissions/149abd55-d54a-4b09-bd06-d5a501b7c3bd

import Mathlib
set_option autoImplicit false

theorem solution {α : Type} [Fintype α] [PartialOrder α] (P : α → Prop) [DecidablePred P] (hP : ∃ a, P a) : ∃ a, P a ∧ ∀ b, P b → a ≤ b → b = a := by
  obtain ⟨a, ha⟩ := hP
  obtain ⟨b, hab, hbmax⟩ := Finite.exists_le_maximal (p := P) ha
  refine ⟨b, hbmax.1, ?_⟩
  intro c hc hbc
  exact le_antisymm (hbmax.2 hc hbc) hbc
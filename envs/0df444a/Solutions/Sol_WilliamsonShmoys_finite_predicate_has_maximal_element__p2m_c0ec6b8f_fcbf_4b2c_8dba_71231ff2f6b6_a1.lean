-- Prove2me | solution 1 for WilliamsonShmoys.finite_predicate_has_maximal_element__p2m_c0ec6b8f_fcbf_4b2c_8dba_71231ff2f6b6_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T08:00:10.445131+00:00
-- url     : https://prove2.me/submissions/6f51de10-f236-4e04-bc48-bb4b7a2b9bd5

import Mathlib

set_option autoImplicit false

universe u

theorem solution
    {α : Type u} [Fintype α] [PartialOrder α]
    (P : α → Prop) (hP : ∃ x, P x) :
    ∃ x, P x ∧ ∀ y, P y → x ≤ y → y ≤ x := by
  obtain ⟨a, ha⟩ := hP
  obtain ⟨b, _, hb⟩ := Finite.exists_le_maximal (p := P) ha
  refine ⟨b, hb.1, ?_⟩
  intro y hy hby
  exact hb.2 hy hby
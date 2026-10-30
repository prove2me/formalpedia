-- Prove2me | solution 1 for WilliamsonShmoys.finite_type_predicate_maximal__p2m_bf001e0e_24f9_43c1_8004_bdc368085703_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:29:45.143888+00:00
-- url     : https://prove2.me/submissions/ae9bc436-f4d5-4f60-8ac9-1bba30abfc74

import Mathlib
set_option autoImplicit false

theorem solution {alpha : Type} [PartialOrder alpha] [Finite alpha]
    (P : alpha → Prop) (hP : ∃ x, P x) :
    ∃ x, P x ∧ ∀ y, P y → x ≤ y → y = x := by
  classical
  obtain ⟨a, ha⟩ := hP
  obtain ⟨x, _, hx⟩ := Finite.exists_le_maximal (p := P) ha
  refine ⟨x, hx.1, ?_⟩
  intro y hy hxy
  exact le_antisymm (hx.2 hy hxy) hxy
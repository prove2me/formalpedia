-- Prove2me | solution 1 for WilliamsonShmoys.finite_poset_has_maximal__p2m_d962869e_258d_4947_a612_83f18b157228_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T09:21:17.098714+00:00
-- url     : https://prove2.me/submissions/61012a12-c832-431a-8b45-3542993e94a0

import Mathlib

theorem solution
    {α : Type} [Fintype α] [PartialOrder α]
    (S : α → Prop) (hS : ∃ x, S x) :
    ∃ x, S x ∧ ∀ y, S y → x ≤ y → y ≤ x := by
  classical
  obtain ⟨x, hx, hmax⟩ := (Set.toFinite {x | S x}).exists_maximal hS
  exact ⟨x, hx, by simpa [Maximal] using hmax⟩
-- Prove2me | solution 1 for WilliamsonShmoys.finite_set_progress_has_good_element__p2m_a6c61c44_359d_4d57_8094_2c2773f7c78b_a1
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-04T16:45:49.51061+00:00
-- url     : https://prove2.me/submissions/916baec6-9365-4a27-b682-478ae47294a1

import Mathlib

theorem solution {α : Type} [Finite α] (s : Set α) (f : α → Nat) (good : α → Prop)
    (hs : s.Nonempty) (hstep : ∀ x ∈ s, ¬ good x → ∃ y ∈ s, f x < f y) :
    ∃ x ∈ s, good x := by
  classical
  have hsfinite : s.Finite := s.toFinite
  obtain ⟨x, hxs, hxmax⟩ := Set.exists_max_image s f hsfinite hs
  refine ⟨x, hxs, ?_⟩
  by_cases hgood : good x
  · exact hgood
  · obtain ⟨y, hys, hxy⟩ := hstep x hxs hgood
    have hy_le : f y ≤ f x := hxmax y hys
    omega

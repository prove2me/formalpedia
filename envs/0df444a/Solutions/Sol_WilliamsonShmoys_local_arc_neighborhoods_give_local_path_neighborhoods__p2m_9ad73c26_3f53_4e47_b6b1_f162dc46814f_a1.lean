-- Prove2me | solution 1 for WilliamsonShmoys.local_arc_neighborhoods_give_local_path_neighborhoods__p2m_9ad73c26_3f53_4e47_b6b1_f162dc46814f_a1
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-17T09:36:18.254211+00:00
-- url     : https://prove2.me/submissions/1a9010a1-4d7d-4a14-8136-e9b56f7e3e2f

import Mathlib
set_option autoImplicit false
theorem WilliamsonShmoys.local_arc_neighborhoods_give_local_path_neighborhoods__p2m_9ad73c26_3f53_4e47_b6b1_f162dc46814f_a1 {X : Type} [MetricSpace X] {s : Set X} (hlocal : ∀ x : s, ∀ U : Set s, IsOpen U → x ∈ U → ∃ V : Set s, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧ ∀ y ∈ V, y ≠ x → ∃ γ : ℝ → s, ContinuousOn γ (Set.Icc 0 1) ∧ Set.InjOn γ (Set.Icc 0 1) ∧ γ 0 = x ∧ γ 1 = y ∧ ∀ t ∈ Set.Icc 0 1, γ t ∈ U) : ∀ x : s, ∀ U : Set s, IsOpen U → x ∈ U → ∃ V : Set s, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧ ∀ y ∈ V, ∃ γ : ℝ → s, ContinuousOn γ (Set.Icc 0 1) ∧ γ 0 = x ∧ γ 1 = y ∧ ∀ t ∈ Set.Icc 0 1, γ t ∈ U := by
  intro x U hU hxU
  obtain ⟨V, hV, hxV, hVU, harc⟩ := hlocal x U hU hxU
  refine ⟨V, hV, hxV, hVU, fun y hy => ?_⟩
  by_cases hyx : y = x
  · subst hyx
    exact ⟨fun _ => y, continuousOn_const, rfl, rfl, fun _ _ => hxU⟩
  · obtain ⟨γ, hγc, _, h0, h1, hU'⟩ := harc y hy hyx
    exact ⟨γ, hγc, h0, h1, hU'⟩

theorem solution {X : Type} [MetricSpace X] {s : Set X} (hlocal : ∀ x : s, ∀ U : Set s, IsOpen U → x ∈ U → ∃ V : Set s, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧ ∀ y ∈ V, y ≠ x → ∃ γ : ℝ → s, ContinuousOn γ (Set.Icc 0 1) ∧ Set.InjOn γ (Set.Icc 0 1) ∧ γ 0 = x ∧ γ 1 = y ∧ ∀ t ∈ Set.Icc 0 1, γ t ∈ U) : ∀ x : s, ∀ U : Set s, IsOpen U → x ∈ U → ∃ V : Set s, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧ ∀ y ∈ V, ∃ γ : ℝ → s, ContinuousOn γ (Set.Icc 0 1) ∧ γ 0 = x ∧ γ 1 = y ∧ ∀ t ∈ Set.Icc 0 1, γ t ∈ U :=
  WilliamsonShmoys.local_arc_neighborhoods_give_local_path_neighborhoods__p2m_9ad73c26_3f53_4e47_b6b1_f162dc46814f_a1 hlocal

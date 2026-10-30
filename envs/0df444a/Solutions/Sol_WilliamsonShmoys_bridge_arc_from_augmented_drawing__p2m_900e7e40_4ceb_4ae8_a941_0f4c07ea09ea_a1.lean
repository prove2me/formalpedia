-- Prove2me | solution 1 for WilliamsonShmoys.bridge_arc_from_augmented_drawing__p2m_900e7e40_4ceb_4ae8_a941_0f4c07ea09ea_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:30:38.974364+00:00
-- url     : https://prove2.me/submissions/ff37d22c-9aee-4831-95f8-a52904c4aac5

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_bridge_geometry_from_augmented_drawing__p2m_c033d288_31ff_4be1_b1bc_393d667d0f16_a2

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G H : SimpleGraph V)
    (x y : V)
    (hxy : ¬ G.Reachable x y)
    (hrel : ∀ u v, H.Adj u v ↔
      G.Adj u v ∨ (u = x ∧ v = y) ∨ (u = y ∧ v = x))
    (hH : HasPlanarDrawingOn H) :
    ∃ (p : V → ℝ × ℝ) (arc : V → V → ℝ → ℝ × ℝ)
      (γ : ℝ → ℝ × ℝ),
      (Function.Injective p ∧
        (∀ u v, u < v → G.Adj u v →
          ContinuousOn (arc u v) (Set.Icc (0 : ℝ) 1) ∧
          Set.InjOn (arc u v) (Set.Icc (0 : ℝ) 1) ∧
          arc u v 0 = p u ∧ arc u v 1 = p v ∧
          ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, arc u v t ≠ p w) ∧
        (∀ u v a b, u < v → a < b → G.Adj u v → G.Adj a b →
          (u, v) ≠ (a, b) →
          ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) 1,
            arc u v t = arc a b s →
              (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1))) ∧
      (ContinuousOn γ (Set.Icc (0 : ℝ) 1) ∧
        Set.InjOn γ (Set.Icc (0 : ℝ) 1) ∧
        γ 0 = p x ∧ γ 1 = p y ∧
        (∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, γ t ≠ p w) ∧
        (∀ u v, u < v → G.Adj u v →
          ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) 1,
            γ t = arc u v s →
              (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1))) := by
  rcases hH with ⟨p, arc, hp, hedge, hcross⟩
  have hgamma :=
    WilliamsonShmoys.bridge_geometry_from_augmented_drawing__p2m_c033d288_31ff_4be1_b1bc_393d667d0f16_a2
      G H x y hxy hrel p arc hp hedge hcross
  refine ⟨p, arc, hgamma.choose, ?_⟩
  constructor
  · constructor
    · exact hp
    · constructor
      · intro u v huv huvG
        exact hedge u v huv ((hrel u v).2 (Or.inl huvG))
      · intro u v a b huv hab huvG habG hne t ht s hs heq
        exact hcross u v a b huv hab
          ((hrel u v).2 (Or.inl huvG))
          ((hrel a b).2 (Or.inl habG)) hne t ht s hs heq
  · exact hgamma.choose_spec
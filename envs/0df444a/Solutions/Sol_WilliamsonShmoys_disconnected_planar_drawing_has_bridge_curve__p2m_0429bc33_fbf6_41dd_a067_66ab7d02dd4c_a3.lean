-- Prove2me | solution 1 for WilliamsonShmoys.disconnected_planar_drawing_has_bridge_curve__p2m_0429bc33_fbf6_41dd_a067_66ab7d02dd4c_a3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:04:12.661015+00:00
-- url     : https://prove2.me/submissions/32b24474-1c29-46ca-9829-578b0bef7022
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_survives_component_bridge__p2m_900e7e40_4ceb_4ae8_a941_0f4c07ea09ea_a1
import Theorems.Thm_WilliamsonShmoys_bridge_arc_from_augmented_drawing__p2m_900e7e40_4ceb_4ae8_a941_0f4c07ea09ea_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G)
    (x y : V)
    (hxy : ¬ G.Reachable x y) :
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
  obtain ⟨H, hrel, hH⟩ :=
    WilliamsonShmoys.planar_drawing_survives_component_bridge__p2m_900e7e40_4ceb_4ae8_a941_0f4c07ea09ea_a1
      G hG x y hxy
  exact
    WilliamsonShmoys.bridge_arc_from_augmented_drawing__p2m_900e7e40_4ceb_4ae8_a941_0f4c07ea09ea_a1
      G H x y hxy hrel hH
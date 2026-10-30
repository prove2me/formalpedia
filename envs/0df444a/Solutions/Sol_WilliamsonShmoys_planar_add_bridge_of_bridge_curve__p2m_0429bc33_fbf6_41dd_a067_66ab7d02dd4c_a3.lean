-- Prove2me | solution 1 for WilliamsonShmoys.planar_add_bridge_of_bridge_curve__p2m_0429bc33_fbf6_41dd_a067_66ab7d02dd4c_a3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:34:46.64099+00:00
-- url     : https://prove2.me/submissions/e4333874-0237-44b1-a803-35a9fe13e899
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_add_bridge_curve_geometry__p2m_02853d91_2027_4c7f_9261_be16db6326ab_a1
import Theorems.Thm_WilliamsonShmoys_bridge_add_graph__p2m_02853d91_2027_4c7f_9261_be16db6326ab_a3

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (x y : V)
    (hxy : ¬ G.Reachable x y)
    (p : V → ℝ × ℝ)
    (arc : V → V → ℝ → ℝ × ℝ)
    (γ : ℝ → ℝ × ℝ)
    (hDrawing :
      Function.Injective p ∧
        (∀ u v, u < v → G.Adj u v →
          ContinuousOn (arc u v) (Set.Icc (0 : ℝ) 1) ∧
          Set.InjOn (arc u v) (Set.Icc (0 : ℝ) 1) ∧
          arc u v 0 = p u ∧ arc u v 1 = p v ∧
          ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, arc u v t ≠ p w) ∧
        (∀ u v a b, u < v → a < b → G.Adj u v → G.Adj a b →
          (u, v) ≠ (a, b) →
          ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) 1,
            arc u v t = arc a b s →
              (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1)))
    (hBridge :
      ContinuousOn γ (Set.Icc (0 : ℝ) 1) ∧
        Set.InjOn γ (Set.Icc (0 : ℝ) 1) ∧
        γ 0 = p x ∧ γ 1 = p y ∧
        (∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, γ t ≠ p w) ∧
        (∀ u v, u < v → G.Adj u v →
          ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) 1,
            γ t = arc u v s →
              (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1))) :
    ∃ N : SimpleGraph V,
      G ≤ N ∧
      (∀ u v, N.Adj u v ↔
        G.Adj u v ∨ ((u = x ∧ v = y) ∨ (u = y ∧ v = x))) ∧
      HasPlanarDrawingOn N := by
  rcases WilliamsonShmoys.bridge_add_graph__p2m_02853d91_2027_4c7f_9261_be16db6326ab_a3
      G x y hxy with ⟨N, hGN, hAdj⟩
  refine ⟨N, hGN, hAdj, ?_⟩
  exact WilliamsonShmoys.planar_add_bridge_curve_geometry__p2m_02853d91_2027_4c7f_9261_be16db6326ab_a1
    G N x y hxy hAdj p arc γ hDrawing hBridge
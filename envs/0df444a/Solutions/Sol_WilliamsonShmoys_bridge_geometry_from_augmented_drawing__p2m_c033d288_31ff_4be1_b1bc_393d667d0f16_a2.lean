-- Prove2me | solution 1 for WilliamsonShmoys.bridge_geometry_from_augmented_drawing__p2m_c033d288_31ff_4be1_b1bc_393d667d0f16_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:45:21.236183+00:00
-- url     : https://prove2.me/submissions/0771c300-5760-489c-b2a3-0298697c6ceb

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_bridge_curve_without_crossings__p2m_19127b46_9641_4d27_850f_f6e2e566cd33_a2
import Theorems.Thm_WilliamsonShmoys_bridge_curve_meets_original_edges__p2m_19127b46_9641_4d27_850f_f6e2e566cd33_a2

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G H : SimpleGraph V) (x y : V)
    (hxy : ¬ G.Reachable x y)
    (hrel : ∀ u v, H.Adj u v ↔
      G.Adj u v ∨ (u = x ∧ v = y) ∨ (u = y ∧ v = x))
    (p : V → ℝ × ℝ) (arc : V → V → ℝ → ℝ × ℝ)
    (hp : Function.Injective p)
    (hedge : ∀ u v, u < v → H.Adj u v →
      ContinuousOn (arc u v) (Set.Icc (0 : ℝ) 1) ∧
      Set.InjOn (arc u v) (Set.Icc (0 : ℝ) 1) ∧
      arc u v 0 = p u ∧ arc u v 1 = p v ∧
      ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, arc u v t ≠ p w)
    (hcross : ∀ u v a b, u < v → a < b → H.Adj u v → H.Adj a b →
      (u, v) ≠ (a, b) →
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) 1,
        arc u v t = arc a b s → (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1)) :
    ∃ γ : ℝ → ℝ × ℝ,
      ContinuousOn γ (Set.Icc (0 : ℝ) 1) ∧
      Set.InjOn γ (Set.Icc (0 : ℝ) 1) ∧
      γ 0 = p x ∧ γ 1 = p y ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, γ t ≠ p w) ∧
      (∀ u v, u < v → G.Adj u v →
        ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) 1,
          γ t = arc u v s → (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1)) := by
  obtain ⟨γ, hcont, hinj, h0, h1, havoid, hrep⟩ :=
    WilliamsonShmoys.bridge_curve_without_crossings__p2m_19127b46_9641_4d27_850f_f6e2e566cd33_a2
      G H x y hxy hrel p arc hp hedge
  have hmeet :=
    WilliamsonShmoys.bridge_curve_meets_original_edges__p2m_19127b46_9641_4d27_850f_f6e2e566cd33_a2
      G H x y hxy hrel arc hcross γ hrep
  exact ⟨γ, hcont, hinj, h0, h1, havoid, hmeet⟩
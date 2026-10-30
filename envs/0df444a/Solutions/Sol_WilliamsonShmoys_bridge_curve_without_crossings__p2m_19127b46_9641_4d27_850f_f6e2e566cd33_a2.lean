-- Prove2me | solution 1 for WilliamsonShmoys.bridge_curve_without_crossings__p2m_19127b46_9641_4d27_850f_f6e2e566cd33_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:58:05.295347+00:00
-- url     : https://prove2.me/submissions/4829d6f7-4cac-4a9b-9ca8-946b233c5943

import Theorems.Thm_WilliamsonShmoys_bridge_curve_forward__p2m_6ebb6941_3575_43d9_99fa_a3f3a344e2d8_a1
import Theorems.Thm_WilliamsonShmoys_bridge_curve_reverse__p2m_6ebb6941_3575_43d9_99fa_a3f3a344e2d8_a1
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

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
      ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, arc u v t ≠ p w) :
    ∃ γ : ℝ → ℝ × ℝ,
      ContinuousOn γ (Set.Icc (0 : ℝ) 1) ∧
      Set.InjOn γ (Set.Icc (0 : ℝ) 1) ∧
      γ 0 = p x ∧ γ 1 = p y ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, γ t ≠ p w) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1,
        γ t = if x < y then arc x y t else arc y x (1 - t)) := by
  by_cases hlt : x < y
  · have hadj : H.Adj x y :=
      (hrel x y).2 (Or.inr (Or.inl ⟨rfl, rfl⟩))
    simpa [hlt] using
      (WilliamsonShmoys.bridge_curve_forward__p2m_6ebb6941_3575_43d9_99fa_a3f3a344e2d8_a1
        (G := G) (H := H) (x := x) (y := y) (p := p) (arc := arc)
        hp hedge hadj hlt)
  · have hyle : y ≤ x := le_of_not_gt hlt
    rcases lt_or_eq_of_le hyle with hrev | heq
    · have hadj : H.Adj y x :=
        (hrel y x).2 (Or.inr (Or.inr ⟨rfl, rfl⟩))
      simpa [hlt] using
        (WilliamsonShmoys.bridge_curve_reverse__p2m_6ebb6941_3575_43d9_99fa_a3f3a344e2d8_a1
          (G := G) (H := H) (x := x) (y := y) (p := p) (arc := arc)
          hp hedge hadj hrev)
    · subst y
      exact False.elim (hxy (SimpleGraph.Reachable.refl x))
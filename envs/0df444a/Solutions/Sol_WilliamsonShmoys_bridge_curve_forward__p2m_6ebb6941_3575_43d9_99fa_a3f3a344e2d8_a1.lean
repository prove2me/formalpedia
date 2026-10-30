-- Prove2me | solution 1 for WilliamsonShmoys.bridge_curve_forward__p2m_6ebb6941_3575_43d9_99fa_a3f3a344e2d8_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T01:00:34.882433+00:00
-- url     : https://prove2.me/submissions/9ce18681-153a-421d-8be3-2a2194822e7e

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G H : SimpleGraph V) (x y : V)
    (p : V → ℝ × ℝ) (arc : V → V → ℝ → ℝ × ℝ)
    (hp : Function.Injective p)
    (hedge : ∀ u v, u < v → H.Adj u v →
      ContinuousOn (arc u v) (Set.Icc (0 : ℝ) 1) ∧
      Set.InjOn (arc u v) (Set.Icc (0 : ℝ) 1) ∧
      arc u v 0 = p u ∧ arc u v 1 = p v ∧
      ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, arc u v t ≠ p w)
    (hadj : H.Adj x y) (hlt : x < y) :
    ∃ γ : ℝ → ℝ × ℝ,
      ContinuousOn γ (Set.Icc (0 : ℝ) 1) ∧
      Set.InjOn γ (Set.Icc (0 : ℝ) 1) ∧
      γ 0 = p x ∧ γ 1 = p y ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, γ t ≠ p w) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, γ t = arc x y t) := by
  refine ⟨arc x y, ?_⟩
  rcases hedge x y hlt hadj with ⟨hcont, hinj, hzero, hone, havoid⟩
  exact ⟨hcont, hinj, hzero, hone, havoid, fun t ht => rfl⟩
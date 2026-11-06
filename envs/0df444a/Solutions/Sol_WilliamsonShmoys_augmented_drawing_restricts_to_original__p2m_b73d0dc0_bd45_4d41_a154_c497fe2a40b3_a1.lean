-- Prove2me | solution 1 for WilliamsonShmoys.augmented_drawing_restricts_to_original__p2m_b73d0dc0_bd45_4d41_a154_c497fe2a40b3_a1
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-05T15:07:50.165295+00:00
-- url     : https://prove2.me/submissions/c473d6c1-20c8-43bb-ab3d-60a937d462fc

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys
set_option autoImplicit false

set_option linter.unusedVariables false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (u v : V)
    (p : V → ℝ × ℝ) (arc : V → V → ℝ → ℝ × ℝ)
    (hp : Function.Injective p)
    (hAugEdge : ∀ a b, a < b →
      (H ⊔ SimpleGraph.fromEdgeSet {s(u, v)}).Adj a b →
        ContinuousOn (arc a b) (Set.Icc 0 1) ∧
        Set.InjOn (arc a b) (Set.Icc 0 1) ∧
        arc a b 0 = p a ∧ arc a b 1 = p b ∧
        ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, arc a b t ≠ p w) :
    ∀ a b, a < b → H.Adj a b →
      ContinuousOn (arc a b) (Set.Icc 0 1) ∧
      Set.InjOn (arc a b) (Set.Icc 0 1) ∧
      arc a b 0 = p a ∧ arc a b 1 = p b ∧
      ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, arc a b t ≠ p w := by
  simp_all

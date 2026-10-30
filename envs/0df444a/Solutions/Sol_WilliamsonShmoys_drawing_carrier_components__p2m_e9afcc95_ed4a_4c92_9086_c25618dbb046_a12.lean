-- Prove2me | solution 1 for WilliamsonShmoys.drawing_carrier_components__p2m_e9afcc95_ed4a_4c92_9086_c25618dbb046_a12
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T22:14:27.435987+00:00
-- url     : https://prove2.me/submissions/1dcedd13-da87-46c2-849d-e93f799507cb

import Definitions.Def_WilliamsonShmoys_DrawingCarrier__p2m_e9afcc95_ed4a_4c92_9086_c25618dbb046_a12
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Theorems.Thm_WilliamsonShmoys_drawing_carrier_is_compact__p2m_188e1412_5b81_4b4f_8125_7b7ad68311d3_a1
import Theorems.Thm_WilliamsonShmoys_carrier_component_of_graph_reachable__p2m_188e1412_5b81_4b4f_8125_7b7ad68311d3_a1
import Theorems.Thm_WilliamsonShmoys_graph_reachable_of_carrier_component__p2m_188e1412_5b81_4b4f_8125_7b7ad68311d3_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (p : V → ℝ × ℝ) (arc : V → V → ℝ → ℝ × ℝ)
    (hp : Function.Injective p)
    (ha : ∀ u v, u < v → G.Adj u v →
      ContinuousOn (arc u v) (Set.Icc 0 1) ∧
      Set.InjOn (arc u v) (Set.Icc 0 1) ∧
      arc u v 0 = p u ∧ arc u v 1 = p v ∧
      ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, arc u v t ≠ p w)
    (hi : ∀ u v x y, u < v → x < y → G.Adj u v → G.Adj x y →
      (u, v) ≠ (x, y) → ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc 0 1,
        arc u v t = arc x y s → (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1)) :
    IsCompact (WilliamsonShmoys_DrawingCarrier__p2m_e9afcc95_ed4a_4c92_9086_c25618dbb046_a12 G p arc) ∧
      ∀ u v : V,
        p v ∈ connectedComponentIn
          (WilliamsonShmoys_DrawingCarrier__p2m_e9afcc95_ed4a_4c92_9086_c25618dbb046_a12 G p arc) (p u) ↔
          G.Reachable u v := by
  constructor
  · exact WilliamsonShmoys.drawing_carrier_is_compact__p2m_188e1412_5b81_4b4f_8125_7b7ad68311d3_a1
      G p arc hp ha hi
  · intro u v
    constructor
    · exact WilliamsonShmoys.graph_reachable_of_carrier_component__p2m_188e1412_5b81_4b4f_8125_7b7ad68311d3_a1
        G p arc hp ha hi u v
    · exact WilliamsonShmoys.carrier_component_of_graph_reachable__p2m_188e1412_5b81_4b4f_8125_7b7ad68311d3_a1
        G p arc hp ha hi u v
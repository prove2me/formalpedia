-- Prove2me | solution 1 for WilliamsonShmoys.connect_planar_drawing__p2m_52d80640_fd16_42f7_b63d_2010f98eda2f_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:28:48.857127+00:00
-- url     : https://prove2.me/submissions/c67f52e3-8a29-45a7-99b3-75e71ea72f96
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_drawing_add_component_bridge__p2m_50046e68_ab20_4f6d_a7b5_2cf104147317_a2
import Theorems.Thm_WilliamsonShmoys_planar_bridge_steps_connect__p2m_50046e68_ab20_4f6d_a7b5_2cf104147317_a2

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ H : SimpleGraph V, K ≤ H ∧ H.Connected ∧
      WilliamsonShmoys.HasPlanarDrawingOn H := by
  exact WilliamsonShmoys.planar_bridge_steps_connect__p2m_50046e68_ab20_4f6d_a7b5_2cf104147317_a2
    K hK (by
      intro G hG hGnot
      exact WilliamsonShmoys.planar_drawing_add_component_bridge__p2m_50046e68_ab20_4f6d_a7b5_2cf104147317_a2
        G hG hGnot)
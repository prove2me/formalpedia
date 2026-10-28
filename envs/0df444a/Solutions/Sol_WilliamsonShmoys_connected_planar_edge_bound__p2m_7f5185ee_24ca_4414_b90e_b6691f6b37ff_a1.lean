-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_edge_bound__p2m_7f5185ee_24ca_4414_b90e_b6691f6b37ff_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T20:31:30.613324+00:00
-- url     : https://prove2.me/submissions/444187e4-df5a-4eb9-a832-0426a08ce6f6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_data__p2m_89f9508a_afd6_4065_9e12_3df1eadb7958_a1
import Theorems.Thm_WilliamsonShmoys_planar_edge_bound_of_euler_data__p2m_89f9508a_afd6_4065_9e12_3df1eadb7958_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hConnected : M.Connected) (hM : HasPlanarDrawingOn M) :
    M.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  obtain ⟨f, hEuler, hFaces⟩ :=
    WilliamsonShmoys.planar_drawing_euler_data__p2m_89f9508a_afd6_4065_9e12_3df1eadb7958_a1
      M hV hConnected hM
  exact WilliamsonShmoys.planar_edge_bound_of_euler_data__p2m_89f9508a_afd6_4065_9e12_3df1eadb7958_a1
    (Fintype.card V) M.edgeSet.ncard f hV hEuler hFaces
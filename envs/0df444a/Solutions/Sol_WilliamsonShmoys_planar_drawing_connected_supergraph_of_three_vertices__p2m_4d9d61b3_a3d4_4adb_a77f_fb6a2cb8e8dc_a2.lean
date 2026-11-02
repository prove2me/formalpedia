-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_connected_supergraph_of_three_vertices__p2m_4d9d61b3_a3d4_4adb_a77f_fb6a2cb8e8dc_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:44:00.549481+00:00
-- url     : https://prove2.me/submissions/38b2f8a5-0a7b-409f-a15d-f2e7b5416858
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planarDrawing_add_cross_component_edge__p2m_dddaee3a_0582_44d9_9566_a5dd1d115710_a1
import Theorems.Thm_WilliamsonShmoys_planarDrawing_connected_supergraph_from_edge_step__p2m_dddaee3a_0582_44d9_9566_a5dd1d115710_a1
import Mathlib

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hn : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      K ≤ H ∧ H.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn H := by
  exact WilliamsonShmoys.planarDrawing_connected_supergraph_from_edge_step__p2m_dddaee3a_0582_44d9_9566_a5dd1d115710_a1
    K hn hK
    (fun G hG hdisconnected =>
      WilliamsonShmoys.planarDrawing_add_cross_component_edge__p2m_dddaee3a_0582_44d9_9566_a5dd1d115710_a1
        G hG hdisconnected)
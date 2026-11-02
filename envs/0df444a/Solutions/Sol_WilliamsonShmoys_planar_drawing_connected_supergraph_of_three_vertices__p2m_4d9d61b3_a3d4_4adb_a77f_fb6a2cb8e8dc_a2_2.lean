-- Prove2me | solution 2 for WilliamsonShmoys.planar_drawing_connected_supergraph_of_three_vertices__p2m_4d9d61b3_a3d4_4adb_a77f_fb6a2cb8e8dc_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T15:55:44.755968+00:00
-- url     : https://prove2.me/submissions/89021bc2-909a-404b-91ae-4cd50333277f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planarDrawing_edge_maximal_supergraph__p2m_dddaee3a_0582_44d9_9566_a5dd1d115710_a2
import Theorems.Thm_WilliamsonShmoys_edge_maximal_planar_graph_connected__p2m_dddaee3a_0582_44d9_9566_a5dd1d115710_a2
import Mathlib

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hn : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      K ≤ H ∧ H.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn H := by
  obtain ⟨M, hKM, hM, hmax⟩ :=
    WilliamsonShmoys.planarDrawing_edge_maximal_supergraph__p2m_dddaee3a_0582_44d9_9566_a5dd1d115710_a2
      K hK
  exact ⟨M, hKM,
    WilliamsonShmoys.edge_maximal_planar_graph_connected__p2m_dddaee3a_0582_44d9_9566_a5dd1d115710_a2
      M hn hM hmax,
    hM⟩
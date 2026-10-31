-- Prove2me | solution 1 for WilliamsonShmoys.planar_graph_has_triangulation_completion__p2m_1d331833_450a_47b6_a107_4143d686327f_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T09:24:53.647576+00:00
-- url     : https://prove2.me/submissions/8b0e25b3-549d-47b6-ae29-9496ecb6bd50

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_maximal_supergraph__p2m_39622fc7_9624_4f8c_802c_be6d654a55c6_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_has_triangulation_edge_count__p2m_39622fc7_9624_4f8c_802c_be6d654a55c6_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hG : HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V, G <= H ∧ HasPlanarDrawingOn H ∧
      H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨H, hGH, hH, hMax⟩ :=
    WilliamsonShmoys.planar_drawing_has_maximal_supergraph__p2m_39622fc7_9624_4f8c_802c_be6d654a55c6_a1
      G hG
  have hCount :=
    WilliamsonShmoys.maximal_planar_drawing_has_triangulation_edge_count__p2m_39622fc7_9624_4f8c_802c_be6d654a55c6_a1
      H hH hV hMax
  exact ⟨H, hGH, hH, hCount⟩
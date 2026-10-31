-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_triangulation__p2m_9786a817_f7aa_4876_b28c_017cd5fca12a_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:25:49.006396+00:00
-- url     : https://prove2.me/submissions/2f34c921-ab7f-4c8d-8de3-69bf60afd3b1

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension__p2m_8874575c_8d28_40c2_984e_f8a2d2056536_a4
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count__p2m_8874575c_8d28_40c2_984e_f8a2d2056536_a4

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H) :
    Exists fun T : SimpleGraph V =>
      H <= T /\ WilliamsonShmoys.HasPlanarDrawingOn T /\
        T.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨T, hHT, hDrawT, hMax⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_extension__p2m_8874575c_8d28_40c2_984e_f8a2d2056536_a4 H hDraw
  exact ⟨T, hHT, hDrawT,
    WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_8874575c_8d28_40c2_984e_f8a2d2056536_a4 T hV hDrawT hMax⟩
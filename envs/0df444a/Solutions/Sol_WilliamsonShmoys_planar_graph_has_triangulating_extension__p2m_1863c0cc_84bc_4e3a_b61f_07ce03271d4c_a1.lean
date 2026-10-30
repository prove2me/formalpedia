-- Prove2me | solution 1 for WilliamsonShmoys.planar_graph_has_triangulating_extension__p2m_1863c0cc_84bc_4e3a_b61f_07ce03271d4c_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:33:18.274867+00:00
-- url     : https://prove2.me/submissions/c09e3ab2-16a9-44f9-b182-9ffba1f56a3d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_maximal_extension__p2m_a5443f4e_9d41_4300_b6d5_4cb884e21163_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_has_triangulation_edge_count__p2m_a5443f4e_9d41_4300_b6d5_4cb884e21163_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn J)
    (hV : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      J ≤ K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      K.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨K, hJK, hDrawK, hMax⟩ :=
    WilliamsonShmoys.planar_drawing_has_maximal_extension__p2m_a5443f4e_9d41_4300_b6d5_4cb884e21163_a1
      J hDraw
  refine ⟨K, hJK, hDrawK, ?_⟩
  exact WilliamsonShmoys.maximal_planar_graph_has_triangulation_edge_count__p2m_a5443f4e_9d41_4300_b6d5_4cb884e21163_a1
    K hDrawK hMax hV
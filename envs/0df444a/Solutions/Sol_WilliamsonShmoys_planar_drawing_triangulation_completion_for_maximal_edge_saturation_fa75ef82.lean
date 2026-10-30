-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_triangulation_completion_for_maximal_edge_saturation_fa75ef82
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T00:55:43.085996+00:00
-- url     : https://prove2.me/submissions/b9895fc8-5835-4fa5-8672-230b6701e3a3

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension_exists__p2m_e8ae6a5a_5a4c_4f53_9707_6853e31c2747_a4
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_e8ae6a5a_5a4c_4f53_9707_6853e31c2747_a4

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hDraw : HasPlanarDrawingOn L)
    (hCard : 3 <= Fintype.card V) :
    Exists fun M : SimpleGraph V => L <= M /\ HasPlanarDrawingOn M /\
      M.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨M, hLM, hMDraw, hMax⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_extension_exists__p2m_e8ae6a5a_5a4c_4f53_9707_6853e31c2747_a4 L hDraw
  exact ⟨M, hLM, hMDraw,
    WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_e8ae6a5a_5a4c_4f53_9707_6853e31c2747_a4 M hMDraw hCard hMax⟩

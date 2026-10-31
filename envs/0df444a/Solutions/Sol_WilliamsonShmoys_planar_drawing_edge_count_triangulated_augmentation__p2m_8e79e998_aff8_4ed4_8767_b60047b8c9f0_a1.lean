-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_count_triangulated_augmentation__p2m_8e79e998_aff8_4ed4_8767_b60047b8c9f0_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:32:46.181299+00:00
-- url     : https://prove2.me/submissions/35c7e224-45dc-47fb-8bd3-aed1b87c8afa
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planarDrawing_has_maximal_supergraph__p2m_ed8fdf3f_bcec_42f4_9879_6d1c022759a1_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_ed8fdf3f_bcec_42f4_9879_6d1c022759a1_a1

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : HasPlanarDrawingOn H)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧ HasPlanarDrawingOn K ∧
      H.edgeSet.ncard ≤ K.edgeSet.ncard ∧
      K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨K, hHK, hK, hEdge, hMax⟩ :=
    WilliamsonShmoys.planarDrawing_has_maximal_supergraph__p2m_ed8fdf3f_bcec_42f4_9879_6d1c022759a1_a1 H hH
  refine ⟨K, hHK, hK, hEdge, ?_⟩
  exact WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_ed8fdf3f_bcec_42f4_9879_6d1c022759a1_a1 K hK hCard hMax
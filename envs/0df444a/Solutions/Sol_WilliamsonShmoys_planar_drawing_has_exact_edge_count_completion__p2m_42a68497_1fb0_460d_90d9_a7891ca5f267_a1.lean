-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_has_exact_edge_count_completion__p2m_42a68497_1fb0_460d_90d9_a7891ca5f267_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T20:00:38.784526+00:00
-- url     : https://prove2.me/submissions/00b41075-e435-4638-baed-ed408e0835ce
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_maximal__p2m_fd3a6d21_9f96_42df_ba7f_14589e74085f_a2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_fd3a6d21_9f96_42df_ba7f_14589e74085f_a2

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 <= Fintype.card V) :
    Exists fun K : SimpleGraph V =>
      Set.Subset G.edgeSet K.edgeSet /\
      WilliamsonShmoys.HasPlanarDrawingOn K /\
      K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨K, hGK, hK, hmax⟩ :=
    WilliamsonShmoys.planar_supergraph_maximal__p2m_fd3a6d21_9f96_42df_ba7f_14589e74085f_a2
      G hG hV
  exact ⟨K, hGK, hK,
    WilliamsonShmoys.maximal_planar_edge_count__p2m_fd3a6d21_9f96_42df_ba7f_14589e74085f_a2
      K hK hmax hV⟩
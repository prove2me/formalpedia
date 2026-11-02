-- Prove2me | solution 1 for WilliamsonShmoys.simple_graph_planar_edge_bound__p2m_8bcf31fc_0140_4078_86ae_c40cd3c611a4_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T06:45:02.985116+00:00
-- url     : https://prove2.me/submissions/1d7adfab-5f79-4b46-be5c-21c49f61fa1a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension__p2m_ddf70dfc_9e43_42b2_878d_a461f3516711_a6
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_simple_graph_edge_bound__p2m_ddf70dfc_9e43_42b2_878d_a461f3516711_a6

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hcard : 3 <= Fintype.card V) :
    (letI : DecidableRel H.Adj := Classical.decRel _
     H.edgeFinset.card + 6 <= 3 * Fintype.card V) := by
  letI : DecidableRel H.Adj := Classical.decRel _
  obtain ⟨K, hHK, hKdraw, hKmax, hcard_le⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_extension__p2m_ddf70dfc_9e43_42b2_878d_a461f3516711_a6 H hH
  have hKbound :=
    WilliamsonShmoys.maximal_drawable_simple_graph_edge_bound__p2m_ddf70dfc_9e43_42b2_878d_a461f3516711_a6 K hKdraw hcard hKmax
  omega
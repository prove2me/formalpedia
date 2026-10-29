-- Prove2me | solution 1 for WilliamsonShmoys.planar_completion_max_edges_from_drawing_e7f6fb70__p2m_58175b1d_a153_41c0_9a66_d5e759d3d2be_a5
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T02:21:42.629873+00:00
-- url     : https://prove2.me/submissions/c8e6613b-b046-48fd-a4cd-b959d9329b6e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_9c6e361c_4d55_4494_87be_52db2dff7ab6_a2
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension__p2m_9c6e361c_4d55_4494_87be_52db2dff7ab6_a2

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    Exists fun K : SimpleGraph V =>
      (forall {u v}, H.Adj u v -> K.Adj u v) /\
      WilliamsonShmoys.HasPlanarDrawingOn K /\
      K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨K, hHK, hK, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_extension__p2m_9c6e361c_4d55_4494_87be_52db2dff7ab6_a2
      H hV hH
  exact ⟨K, hHK, hK,
    WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_9c6e361c_4d55_4494_87be_52db2dff7ab6_a2
      K hV hK hmax⟩
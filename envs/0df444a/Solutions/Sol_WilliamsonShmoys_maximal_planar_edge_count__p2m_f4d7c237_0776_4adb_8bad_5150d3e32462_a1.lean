-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_f4d7c237_0776_4adb_8bad_5150d3e32462_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T22:17:02.693213+00:00
-- url     : https://prove2.me/submissions/bb2de455-84fb-4b88-af0f-f79f6f92c436

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bound__p2m_3b70d152_dbfb_4f09_8d03_767be9da3cd3_a2

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hcard : 3 <= Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : forall K : SimpleGraph V, H.edgeSet ⊆ K.edgeSet ->
      WilliamsonShmoys.HasPlanarDrawingOn K -> K.edgeSet = H.edgeSet) :
    H.edgeSet.ncard <= 3 * Fintype.card V - 6 := by
  exact WilliamsonShmoys.planar_drawing_edge_bound__p2m_3b70d152_dbfb_4f09_8d03_767be9da3cd3_a2
    H hcard hH
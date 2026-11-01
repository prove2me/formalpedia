-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_bound__p2m_602c691a_8d1a_4dfe_88c6_7f0f95c89b91_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:36:19.16006+00:00
-- url     : https://prove2.me/submissions/96b31e12-94b7-4154-96a7-3d53135a179f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_simple_graph_planar_edge_bound__p2m_8bcf31fc_0140_4078_86ae_c40cd3c611a4_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : forall K : SimpleGraph V, H <= K ->
      WilliamsonShmoys.HasPlanarDrawingOn K -> K = H)
    (hcard : 3 <= Fintype.card V) :
    (letI : DecidableRel H.Adj := Classical.decRel _
     H.edgeFinset.card + 6 <= 3 * Fintype.card V) := by
  letI : DecidableRel H.Adj := Classical.decRel _
  exact WilliamsonShmoys.simple_graph_planar_edge_bound__p2m_8bcf31fc_0140_4078_86ae_c40cd3c611a4_a1 H hH hcard
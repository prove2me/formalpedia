-- Prove2me | solution 1 for WilliamsonShmoys.planar_simple_graph_edge_count_le__p2m_3fc01ea4_45ff_4122_aa0a_4406b31c4da5_a3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T08:25:41.59734+00:00
-- url     : https://prove2.me/submissions/73efd906-afb3-481e-9a75-fdffed35fab9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_planar_triangulation_extension__p2m_92ca81a2_db32_4d33_9bc5_e52120cf72bb_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hHdraw : WilliamsonShmoys.HasPlanarDrawingOn H) :
    (letI : DecidableRel H.Adj := Classical.decRel H.Adj
     H.edgeFinset.card ≤ 3 * Fintype.card V - 6) := by
  classical
  obtain ⟨G, _hHG, _hGdraw, hle, hGcard⟩ :=
    WilliamsonShmoys.exists_planar_triangulation_extension__p2m_92ca81a2_db32_4d33_9bc5_e52120cf72bb_a1
      H hcard hHdraw
  exact hle.trans_eq hGcard
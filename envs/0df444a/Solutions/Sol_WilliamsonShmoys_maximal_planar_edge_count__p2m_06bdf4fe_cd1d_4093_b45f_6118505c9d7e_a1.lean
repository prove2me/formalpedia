-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_06bdf4fe_cd1d_4093_b45f_6118505c9d7e_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T08:11:53.527536+00:00
-- url     : https://prove2.me/submissions/b9bc3c7e-383d-4918-9538-95b46c62e06c

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_count_le__p2m_3fc01ea4_45ff_4122_aa0a_4406b31c4da5_a3
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_ge__p2m_3fc01ea4_45ff_4122_aa0a_4406b31c4da5_a3

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hHconn : H.Connected)
    (hHdraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hHmax : ∀ J : SimpleGraph V, H ≤ J →
      WilliamsonShmoys.HasPlanarDrawingOn J → J ≤ H) :
    (letI : DecidableRel H.Adj := Classical.decRel H.Adj
     H.edgeFinset.card = 3 * Fintype.card V - 6) := by
  letI : DecidableRel H.Adj := Classical.decRel H.Adj
  have hup :
      H.edgeFinset.card ≤ 3 * Fintype.card V - 6 :=
    WilliamsonShmoys.planar_simple_graph_edge_count_le__p2m_3fc01ea4_45ff_4122_aa0a_4406b31c4da5_a3
      H hcard hHdraw
  have hlo :
      3 * Fintype.card V - 6 ≤ H.edgeFinset.card :=
    WilliamsonShmoys.maximal_planar_edge_count_ge__p2m_3fc01ea4_45ff_4122_aa0a_4406b31c4da5_a3
      H hcard hHconn hHdraw hHmax
  omega

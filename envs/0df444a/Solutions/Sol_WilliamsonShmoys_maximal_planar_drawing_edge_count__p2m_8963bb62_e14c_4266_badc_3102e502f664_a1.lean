-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_8963bb62_e14c_4266_badc_3102e502f664_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-03T16:37:46.239609+00:00
-- url     : https://prove2.me/submissions/27820d64-a9b4-45ba-be38-0a9ecb38f874

import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_has_euler_edge_count_e02108dc_5749_4b8c_85cc_e86e3f71cac7

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hH : HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V)
    (hMax : ∀ J : SimpleGraph V, HasPlanarDrawingOn J →
      (∀ u v, H.Adj u v → J.Adj u v) →
      (∀ u v, J.Adj u v → H.Adj u v)) :
    H.edgeFinset.card = 3 * Fintype.card V - 6 := by
  have hm : ∀ J : SimpleGraph V, H ≤ J → HasPlanarDrawingOn J → J ≤ H := by
    intro J hsub hdraw
    apply SimpleGraph.le_iff_adj.mpr
    exact hMax J hdraw (SimpleGraph.le_iff_adj.mp hsub)
  have hc := maximal_drawable_graph_has_euler_edge_count_e02108dc_5749_4b8c_85cc_e86e3f71cac7 H hH hV hm
  rw [← H.coe_edgeFinset, Set.ncard_coe_finset] at hc
  omega
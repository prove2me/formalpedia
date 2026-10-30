-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_completion_edge_count_7369a359__p2m_57f967cc_933c_4757_9db5_f93a97c57bfc_a2__p2m_57f967cc_933c_4757_9db5_f93a97c57bfc_a3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T22:06:31.857044+00:00
-- url     : https://prove2.me/submissions/e3af6b3d-1dc8-44aa-ade0-30fd14623971

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_completion_lower_edge_bound__p2m_e54967e0_7450_4934_8f48_f373227ab333_a1
import Theorems.Thm_WilliamsonShmoys_planar_graph_upper_edge_bound__p2m_e54967e0_7450_4934_8f48_f373227ab333_a1

set_option autoImplicit false

open SimpleGraph

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hV : 3 <= Fintype.card V)
    (hMax : forall N : SimpleGraph V, L <= N -> WilliamsonShmoys.HasPlanarDrawingOn N -> N <= L) :
    L.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hlow := WilliamsonShmoys.maximal_planar_completion_lower_edge_bound__p2m_e54967e0_7450_4934_8f48_f373227ab333_a1
    L hL hV hMax
  have hupp := WilliamsonShmoys.planar_graph_upper_edge_bound__p2m_e54967e0_7450_4934_8f48_f373227ab333_a1
    L hL hV
  omega
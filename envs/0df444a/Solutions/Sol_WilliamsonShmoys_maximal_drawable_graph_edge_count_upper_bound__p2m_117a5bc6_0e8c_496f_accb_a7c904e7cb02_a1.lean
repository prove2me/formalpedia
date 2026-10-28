-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_graph_edge_count_upper_bound__p2m_117a5bc6_0e8c_496f_accb_a7c904e7cb02_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T19:14:24.428983+00:00
-- url     : https://prove2.me/submissions/e5375c51-2619-4222-b352-9b45b46f0508
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_components_connected_extension__p2m_9f456864_72ae_4080_90f1_6ccbf874f47a_a2
import Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_euler_certificate__p2m_9f456864_72ae_4080_90f1_6ccbf874f47a_a2
import Theorems.Thm_WilliamsonShmoys_euler_certificate_monotone_edge_bound__p2m_9f456864_72ae_4080_90f1_6ccbf874f47a_a2

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V) :
    L.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨H, hLH, hHconn, hHdraw⟩ :=
    WilliamsonShmoys.planar_drawing_components_connected_extension__p2m_9f456864_72ae_4080_90f1_6ccbf874f47a_a2
      L hL hCard
  have hcert :=
    WilliamsonShmoys.connected_planar_drawing_euler_certificate__p2m_9f456864_72ae_4080_90f1_6ccbf874f47a_a2
      H hHconn hHdraw hCard
  exact
    WilliamsonShmoys.euler_certificate_monotone_edge_bound__p2m_9f456864_72ae_4080_90f1_6ccbf874f47a_a2
      L H hLH hCard hcert
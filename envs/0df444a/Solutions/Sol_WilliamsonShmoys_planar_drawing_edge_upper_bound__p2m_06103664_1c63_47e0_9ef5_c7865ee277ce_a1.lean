-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_upper_bound__p2m_06103664_1c63_47e0_9ef5_c7865ee277ce_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:56:37.172974+00:00
-- url     : https://prove2.me/submissions/87d65a5f-81d6-427a-97ac-8180fe259ee6

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_extension_bound__p2m_76736e59_4cf5_41fe_b0de_3723f7df5ba6_a1
import Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_edge_bound__p2m_76736e59_4cf5_41fe_b0de_3723f7df5ba6_a1

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V) :
    H.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  obtain ⟨K, _hSub, hConn, hKDraw, hCard⟩ :=
    WilliamsonShmoys.planar_drawing_connected_extension_bound__p2m_76736e59_4cf5_41fe_b0de_3723f7df5ba6_a1
      H hDraw hV
  have hBound :=
    WilliamsonShmoys.connected_planar_drawing_edge_bound__p2m_76736e59_4cf5_41fe_b0de_3723f7df5ba6_a1
      K hConn hKDraw hV
  exact le_trans hCard hBound

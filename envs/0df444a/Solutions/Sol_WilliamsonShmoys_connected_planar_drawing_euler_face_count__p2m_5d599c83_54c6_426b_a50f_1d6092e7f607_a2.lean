-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_drawing_euler_face_count__p2m_5d599c83_54c6_426b_a50f_1d6092e7f607_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:23:12.148716+00:00
-- url     : https://prove2.me/submissions/25007a67-55e0-47bf-b025-d6ea3e5b0abd

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bound__p2m_de964016_c5d1_4655_a9b8_5775a5593d8f_a1
import Theorems.Thm_WilliamsonShmoys_connected_edge_count_lower_bound__p2m_de964016_c5d1_4655_a9b8_5775a5593d8f_a1

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hConn : H.Connected)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V) :
    ∃ f : Nat, Fintype.card V + f = H.edgeSet.ncard + 2 ∧
      3 * f ≤ 2 * H.edgeSet.ncard := by
  have hlow : Fintype.card V ≤ H.edgeSet.ncard + 1 :=
    WilliamsonShmoys.connected_edge_count_lower_bound__p2m_de964016_c5d1_4655_a9b8_5775a5593d8f_a1 H hConn
  have hplanar : H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V :=
    WilliamsonShmoys.planar_drawing_edge_bound__p2m_de964016_c5d1_4655_a9b8_5775a5593d8f_a1 H hDraw hV
  refine ⟨H.edgeSet.ncard + 2 - Fintype.card V, ?_, ?_⟩ <;> omega
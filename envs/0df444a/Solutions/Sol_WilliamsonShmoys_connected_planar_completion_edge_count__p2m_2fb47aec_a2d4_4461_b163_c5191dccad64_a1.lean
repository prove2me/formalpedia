-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_completion_edge_count__p2m_2fb47aec_a2d4_4461_b163_c5191dccad64_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T09:52:58.318277+00:00
-- url     : https://prove2.me/submissions/9b559074-319d-4890-9ed6-6746ae2c037b

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension__p2m_5f0f808e_c07c_4234_8a22_35ebffc68b17_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_5f0f808e_c07c_4234_8a22_35ebffc68b17_a1

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hConn : K.Connected)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ H : SimpleGraph V, K ≤ H ∧
      H.edgeSet.ncard = 3 * Fintype.card V - 6 ∧
      WilliamsonShmoys.HasPlanarDrawingOn H := by
  obtain ⟨H, hKH, hH, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_extension__p2m_5f0f808e_c07c_4234_8a22_35ebffc68b17_a1 K hK
  exact ⟨H, hKH,
    WilliamsonShmoys.maximal_planar_edge_count__p2m_5f0f808e_c07c_4234_8a22_35ebffc68b17_a1 H hV hH hmax,
    hH⟩
-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_connected_extension__p2m_f1a10c6f_98ea_4f43_9f3f_2fa486717043_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T22:04:00.83706+00:00
-- url     : https://prove2.me/submissions/3fbca9ca-6595-4f4c-9ccb-7f0af0d281c0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_drawing_add_edge_between_unreachable__p2m_69b1ec23_7e07_4ae5_a2a3_1213925ce8f9_a1
import Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_extension_from_local_addition__p2m_69b1ec23_7e07_4ae5_a2a3_1213925ce8f9_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K) :
    ∃ H : SimpleGraph V,
      HasPlanarDrawingOn H ∧ H.Connected ∧ K.edgeSet.ncard ≤ H.edgeSet.ncard := by
  exact WilliamsonShmoys.planar_drawing_connected_extension_from_local_addition__p2m_69b1ec23_7e07_4ae5_a2a3_1213925ce8f9_a1
    K hK
    (by
      intro G hG hNotConnected
      exact WilliamsonShmoys.planar_drawing_add_edge_between_unreachable__p2m_69b1ec23_7e07_4ae5_a2a3_1213925ce8f9_a1
        G hG hNotConnected)
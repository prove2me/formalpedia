-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_bound__p2m_dbab630e_c01d_4b47_9ab6_dd56c8211fc8_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T09:15:56.366681+00:00
-- url     : https://prove2.me/submissions/d6d20427-90c9-4f6c-bf42-12806d63ba71
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_euler_face_count__p2m_4c27668b_2681_4160_a7ae_a19f29ed8ce0_a1

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hConn : K.Connected)
    (hK : HasPlanarDrawingOn K)
    (hCard : 3 <= Fintype.card V) :
    K.edgeSet.ncard + 6 <= 3 * Fintype.card V := by
  obtain ⟨f, hfBoundary, hfEuler⟩ :=
    WilliamsonShmoys.planar_euler_face_count__p2m_4c27668b_2681_4160_a7ae_a19f29ed8ce0_a1
      K hConn hK hCard
  omega
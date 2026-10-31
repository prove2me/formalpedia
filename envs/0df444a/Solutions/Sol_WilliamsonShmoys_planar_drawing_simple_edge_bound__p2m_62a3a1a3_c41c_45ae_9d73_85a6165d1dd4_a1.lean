-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_simple_edge_bound__p2m_62a3a1a3_c41c_45ae_9d73_85a6165d1dd4_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T09:52:27.263998+00:00
-- url     : https://prove2.me/submissions/ccb1bcbc-fc1c-45c8-8f8e-fd9c4a650c75

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_data__p2m_7318f0dd_6f83_40ec_a6c0_abefe8861b38_a2

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hconn : G.Connected)
    (hCard : 3 ≤ Fintype.card V) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨f, hEuler, hFace⟩ :=
    WilliamsonShmoys.planar_drawing_euler_data__p2m_7318f0dd_6f83_40ec_a6c0_abefe8861b38_a2
      G hG hconn hCard
  omega
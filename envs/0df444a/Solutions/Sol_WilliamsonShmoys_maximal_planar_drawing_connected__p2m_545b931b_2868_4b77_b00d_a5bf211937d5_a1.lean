-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_connected__p2m_545b931b_2868_4b77_b00d_a5bf211937d5_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T19:26:41.497895+00:00
-- url     : https://prove2.me/submissions/a1f130dd-3dfd-4e8e-9e72-b3ce65d32ee4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawingOn_disconnected_strict_extension__p2m_bb4fff64_74f4_4b90_94e5_c66daa170ebe_a1

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hCard : 3 ≤ Fintype.card V)
    (hMaximal : ∀ N : SimpleGraph V,
      M.edgeSet ⊆ N.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn N →
      N.edgeSet ⊆ M.edgeSet) :
    M.Connected := by
  classical
  by_contra hDisconnected
  obtain ⟨N, hMN, hNotNM, hN⟩ :=
    WilliamsonShmoys.planar_drawingOn_disconnected_strict_extension__p2m_bb4fff64_74f4_4b90_94e5_c66daa170ebe_a1
      M hM hDisconnected
  exact hNotNM (hMaximal N hMN hN)
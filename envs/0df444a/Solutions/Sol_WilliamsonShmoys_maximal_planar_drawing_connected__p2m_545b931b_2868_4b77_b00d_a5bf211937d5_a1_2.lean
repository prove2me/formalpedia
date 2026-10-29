-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_drawing_connected__p2m_545b931b_2868_4b77_b00d_a5bf211937d5_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T22:07:33.32998+00:00
-- url     : https://prove2.me/submissions/94970106-53da-4202-9012-d4ad7b94e648
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawingOn_disconnected_strict_extension__p2m_bb4fff64_74f4_4b90_94e5_c66daa170ebe_a2

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
    WilliamsonShmoys.planar_drawingOn_disconnected_strict_extension__p2m_bb4fff64_74f4_4b90_94e5_c66daa170ebe_a2
      M hM hCard hDisconnected
  exact hNotNM (hMaximal N hMN hN)
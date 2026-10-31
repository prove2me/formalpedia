-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_2facc1d9_8574_46e5_b6ec_a0ba2784b822_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T09:39:47.962148+00:00
-- url     : https://prove2.me/submissions/1b4b7cf3-0f90-47fb-8053-1ea9fdec9251
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_connected__p2m_2fb47aec_a2d4_4461_b163_c5191dccad64_a1
import Theorems.Thm_WilliamsonShmoys_connected_planar_completion_edge_count__p2m_2fb47aec_a2d4_4461_b163_c5191dccad64_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hMax : ∀ H : SimpleGraph V, L ≤ H →
      WilliamsonShmoys.HasPlanarDrawingOn H → H ≤ L)
    (hV : 3 ≤ Fintype.card V) :
    L.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hConn := WilliamsonShmoys.maximal_drawable_connected__p2m_2fb47aec_a2d4_4461_b163_c5191dccad64_a1
    L hL hMax hV
  obtain ⟨H, hLH, hCount, hH⟩ :=
    WilliamsonShmoys.connected_planar_completion_edge_count__p2m_2fb47aec_a2d4_4461_b163_c5191dccad64_a1
      L hV hConn hL
  have hHL : H ≤ L := hMax H hLH hH
  have hEq : H = L := le_antisymm hHL hLH
  rw [← hEq]
  omega
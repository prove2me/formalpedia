-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_upper__p2m_7b71df04_d9fa_431d_9970_a3959e705ba4_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T17:37:13.590483+00:00
-- url     : https://prove2.me/submissions/b7e2dbc8-841a-4f79-94fa-67c3de4d55eb
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_connected_planar_edge_count_upper__p2m_c46714b6_9bfd_40bf_95c8_08d778b86369_a1
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_from_connected_components__p2m_c46714b6_9bfd_40bf_95c8_08d778b86369_a1
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hplanar : HasPlanarDrawingOn H) :
    H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  exact WilliamsonShmoys.planar_edge_count_from_connected_components__p2m_c46714b6_9bfd_40bf_95c8_08d778b86369_a1
    H hcard hplanar
    (by
      intro W instF instO K hn hconn hdraw
      exact WilliamsonShmoys.connected_planar_edge_count_upper__p2m_c46714b6_9bfd_40bf_95c8_08d778b86369_a1
        K hn hconn hdraw)
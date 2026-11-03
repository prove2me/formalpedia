-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_edge_count_upper__p2m_c46714b6_9bfd_40bf_95c8_08d778b86369_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-02T16:14:21.243873+00:00
-- url     : https://prove2.me/submissions/11336370-38b8-463a-b147-7f0f6115a8cf

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_connected_c61b3391
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hconn : H.Connected) (hplanar : HasPlanarDrawingOn H) :
    H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  have h := WilliamsonShmoys.planar_edge_count_upper_bound_connected_c61b3391
    H hcard hconn hplanar
  omega
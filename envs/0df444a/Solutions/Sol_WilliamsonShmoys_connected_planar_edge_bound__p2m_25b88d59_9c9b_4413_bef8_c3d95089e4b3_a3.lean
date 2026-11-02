-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_edge_bound__p2m_25b88d59_9c9b_4413_bef8_c3d95089e4b3_a3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:29:48.283802+00:00
-- url     : https://prove2.me/submissions/b2e88be0-4c32-415c-8260-2cabe70b55f8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_connected_planar_face_count__p2m_69e73f60_1756_4e30_afbd_efe3ac2bd3ed_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hconn : N.Connected) :
    (letI : DecidableRel N.Adj := Classical.decRel N.Adj
     N.edgeFinset.card ≤ 3 * Fintype.card V - 6) := by
  letI : DecidableRel N.Adj := Classical.decRel N.Adj
  obtain ⟨f, hEuler, hFaces⟩ :=
    WilliamsonShmoys.connected_planar_face_count__p2m_69e73f60_1756_4e30_afbd_efe3ac2bd3ed_a1
      N hcard hN hconn
  omega
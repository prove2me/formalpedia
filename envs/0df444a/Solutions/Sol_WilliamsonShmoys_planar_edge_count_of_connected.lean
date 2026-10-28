-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_of_connected
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T01:14:42.007855+00:00
-- url     : https://prove2.me/submissions/09bafc38-c0b3-4112-b80c-aaa2b2f1d677
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_planar_connected_euler_face_bound

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hconn : G.Connected)
    (hV : 3 ≤ Fintype.card V) :
    G.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  obtain ⟨f, heuler, hfaces⟩ :=
    WilliamsonShmoys.planar_connected_euler_face_bound G hG hconn hV
  omega
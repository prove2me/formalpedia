-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_edge_upper__p2m_f85cf95c_259e_403f_a3bb_5b4078926a26_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:57:41.757754+00:00
-- url     : https://prove2.me/submissions/5bd4b974-3330-4310-97b9-38db63707382
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_connected_planar_triangulation_extension__p2m_cb34eb69_c1b1_45f4_b656_1b9a22fd4b69_a1
import Mathlib
open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V) (hconn : H.Connected)
    (hH : HasPlanarDrawingOn H) :
    H.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  obtain ⟨K, hsub, hdraw, hle, hK⟩ :=
    WilliamsonShmoys.connected_planar_triangulation_extension__p2m_cb34eb69_c1b1_45f4_b656_1b9a22fd4b69_a1
      H hV hconn hH
  omega
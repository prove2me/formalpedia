-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_edge_bound__p2m_9e7a5396_2787_4caf_938c_608408887b08_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:22:36.594876+00:00
-- url     : https://prove2.me/submissions/7e238b11-4051-446c-a10b-25c2972a3a3a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_connected_planar_face_count__p2m_46140569_4e36_49c3_b704_27def16a2d74_a2

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hplanar : HasPlanarDrawingOn H)
    (hconnected : H.Connected)
    (hV : 3 <= Fintype.card V) :
    H.edgeSet.ncard + 6 <= 3 * Fintype.card V := by
  obtain ⟨F, hEuler, hFaceLength⟩ :=
    WilliamsonShmoys.connected_planar_face_count__p2m_46140569_4e36_49c3_b704_27def16a2d74_a2
      H hplanar hconnected hV
  omega
-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_bound_connected__p2m_1e99581f_fcbc_4e9a_9e15_d8d615ea77d1_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:03:06.659658+00:00
-- url     : https://prove2.me/submissions/4f65fb34-68a7-456f-b0d7-7b57cd0e1651
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_face_data__p2m_610b0216_a272_4b4e_8618_1ead071ef542_a2
import Theorems.Thm_WilliamsonShmoys_edge_bound_from_euler_face_data__p2m_610b0216_a272_4b4e_8618_1ead071ef542_a2
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hplanar : HasPlanarDrawingOn H)
    (hconn : H.Connected)
    (hV : 3 ≤ Fintype.card V) :
    H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  classical
  obtain ⟨q, face, hD, hEuler, hFaces⟩ :=
    WilliamsonShmoys.planar_drawing_euler_face_data__p2m_610b0216_a272_4b4e_8618_1ead071ef542_a2
      H hplanar hconn hV
  exact WilliamsonShmoys.edge_bound_from_euler_face_data__p2m_610b0216_a272_4b4e_8618_1ead071ef542_a2
    (Fintype.card V) q H.edgeSet.ncard
    {e : V × V // H.Adj e.1 e.2} face hD hEuler hFaces
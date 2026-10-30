-- Prove2me | solution 2 for WilliamsonShmoys.connected_drawing_euler_face_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T11:16:50.913254+00:00
-- url     : https://prove2.me/submissions/ae80f2a6-2743-4888-a994-f53cf07735d2

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_connected_drawing_euler_and_face_degree_bound__p2m_41c4318d_ce97_4723_a74a_87f78274716c_a4

set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hconn : G.Connected)
    (hV : 3 <= Fintype.card V) :
    exists f : Nat,
      Fintype.card V + f = G.edgeSet.ncard + 2 /\
      3 * f <= 2 * G.edgeSet.ncard := by
  first
  | exact _root_.WilliamsonShmoys.connected_drawing_euler_and_face_degree_bound__p2m_41c4318d_ce97_4723_a74a_87f78274716c_a4
  | (apply _root_.WilliamsonShmoys.connected_drawing_euler_and_face_degree_bound__p2m_41c4318d_ce97_4723_a74a_87f78274716c_a4 <;> assumption)
  | (intros; apply _root_.WilliamsonShmoys.connected_drawing_euler_and_face_degree_bound__p2m_41c4318d_ce97_4723_a74a_87f78274716c_a4 <;> assumption)

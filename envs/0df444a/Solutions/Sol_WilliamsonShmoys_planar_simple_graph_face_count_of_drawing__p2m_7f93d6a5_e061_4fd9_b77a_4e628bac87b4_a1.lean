-- Prove2me | solution 1 for WilliamsonShmoys.planar_simple_graph_face_count_of_drawing__p2m_7f93d6a5_e061_4fd9_b77a_4e628bac87b4_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:47:10.051198+00:00
-- url     : https://prove2.me/submissions/02f82ff3-15e2-4a8c-9bbd-133538548a3a

import Theorems.Thm_WilliamsonShmoys_connected_drawing_euler_face_bound

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) (hconn : H.Connected)
    (hV : 3 ≤ Fintype.card V) :
    ∃ f : ℕ, Fintype.card V + f = H.edgeSet.ncard + 2 ∧
      3 * f ≤ 2 * H.edgeSet.ncard :=
  WilliamsonShmoys.connected_drawing_euler_face_bound H hH hconn hV

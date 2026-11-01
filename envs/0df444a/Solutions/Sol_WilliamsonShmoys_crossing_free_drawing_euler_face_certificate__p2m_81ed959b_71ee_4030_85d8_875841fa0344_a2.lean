-- Prove2me | solution 1 for WilliamsonShmoys.crossing_free_drawing_euler_face_certificate__p2m_81ed959b_71ee_4030_85d8_875841fa0344_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:43:47.318225+00:00
-- url     : https://prove2.me/submissions/64b19232-a5e9-427a-9c28-57b497d40cc9

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_crossing_free_drawing_euler_face_count__p2m_85154c6b_7137_4d28_9cf8_ac3f60076d56_a2
import Theorems.Thm_WilliamsonShmoys_crossing_free_drawing_edge_bound__p2m_85154c6b_7137_4d28_9cf8_ac3f60076d56_a2

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : HasPlanarDrawingOn H)
    (hconn : H.Connected)
    (hcard : 3 <= Fintype.card V) :
    exists f : Nat,
      H.edgeSet.ncard + 2 = Fintype.card V + f /\
      3 * f <= 2 * H.edgeSet.ncard := by
  obtain ⟨f, heuler⟩ :=
    WilliamsonShmoys.crossing_free_drawing_euler_face_count__p2m_85154c6b_7137_4d28_9cf8_ac3f60076d56_a2
      H hH hconn
  have hedge :=
    WilliamsonShmoys.crossing_free_drawing_edge_bound__p2m_85154c6b_7137_4d28_9cf8_ac3f60076d56_a2
      H hH hconn hcard
  refine ⟨f, heuler, ?_⟩
  omega
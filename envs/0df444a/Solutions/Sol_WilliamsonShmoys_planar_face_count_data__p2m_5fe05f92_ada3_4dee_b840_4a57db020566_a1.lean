-- Prove2me | solution 1 for WilliamsonShmoys.planar_face_count_data__p2m_5fe05f92_ada3_4dee_b840_4a57db020566_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:55:20.897044+00:00
-- url     : https://prove2.me/submissions/237e804b-cd1b-40a3-b9f0-34a9b24fc2e6

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_euler_count__p2m_8494d434_ba1f_46ca_922b_9ced4cfa5b5b_a1
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_bound__p2m_8494d434_ba1f_46ca_922b_9ced4cfa5b5b_a2

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hplanar : HasPlanarDrawingOn H)
    (hconnected : H.Connected)
    (hV : 3 <= Fintype.card V) :
    ∃ f : Nat,
      3 * f <= 2 * H.edgeSet.ncard ∧
      Fintype.card V + f = H.edgeSet.ncard + 2 := by
  obtain ⟨f, heuler⟩ :=
    WilliamsonShmoys.planar_euler_count__p2m_8494d434_ba1f_46ca_922b_9ced4cfa5b5b_a1
      H hplanar hconnected hV
  have hedge :=
    WilliamsonShmoys.planar_edge_count_bound__p2m_8494d434_ba1f_46ca_922b_9ced4cfa5b5b_a2
      H hplanar hconnected hV
  exact ⟨f, by omega, heuler⟩
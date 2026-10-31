-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_bound__p2m_714e0d6d_4b4e_4713_bad3_a0723dae3971_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:39:14.013745+00:00
-- url     : https://prove2.me/submissions/f09e8885-3d10-4235-9834-5ab83e4556b5

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_face_count_data__p2m_5fe05f92_ada3_4dee_b840_4a57db020566_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hplanar : HasPlanarDrawingOn H)
    (hconnected : H.Connected)
    (hV : 3 <= Fintype.card V) :
    H.edgeSet.ncard + 6 <= 3 * Fintype.card V := by
  obtain ⟨f, hfaces, heuler⟩ :=
    WilliamsonShmoys.planar_face_count_data__p2m_5fe05f92_ada3_4dee_b840_4a57db020566_a1
      H hplanar hconnected hV
  omega
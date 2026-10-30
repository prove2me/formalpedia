-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_simple_edge_bound__p2m_a9940316_9fb7_49d9_9418_23da2bfccc13_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:53:42.614283+00:00
-- url     : https://prove2.me/submissions/a7db2f3f-07a4-4c28-b6a4-64b2ec8ffc56

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_face_data__p2m_30c809bc_d869_43a8_8404_fcf85ec28b0f_a1
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hT : WilliamsonShmoys.HasPlanarDrawingOn T)
    (hconn : T.Connected) :
    (T.edgeSet.ncard : ℤ) + 6 ≤ 3 * (Fintype.card V : ℤ) := by
  obtain ⟨f, hEuler, hFaces⟩ :=
    WilliamsonShmoys.planar_drawing_euler_face_data__p2m_30c809bc_d869_43a8_8404_fcf85ec28b0f_a1
      T hV hT hconn
  nlinarith
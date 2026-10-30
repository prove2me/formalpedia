-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_face_count_certificate__p2m_cfd012c7_8a6d_483e_9797_29a733a7d0a7_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:43:50.588833+00:00
-- url     : https://prove2.me/submissions/f1f8f440-79fc-42f0-a457-1350e0e242d3

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_face_count__p2m_a9940316_9fb7_49d9_9418_23da2bfccc13_a1
import Theorems.Thm_WilliamsonShmoys_planar_drawing_simple_edge_bound__p2m_a9940316_9fb7_49d9_9418_23da2bfccc13_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hT : WilliamsonShmoys.HasPlanarDrawingOn T) (hconn : T.Connected) :
    ∃ f : ℤ, (Fintype.card V : ℤ) - (T.edgeSet.ncard : ℤ) + f = 2 ∧
      3 * f ≤ 2 * (T.edgeSet.ncard : ℤ) := by
  obtain ⟨f, hEuler⟩ :=
    WilliamsonShmoys.planar_drawing_euler_face_count__p2m_a9940316_9fb7_49d9_9418_23da2bfccc13_a1
      T hT hconn
  have hEdges :=
    WilliamsonShmoys.planar_drawing_simple_edge_bound__p2m_a9940316_9fb7_49d9_9418_23da2bfccc13_a1
      T hV hT hconn
  exact ⟨f, hEuler, by omega⟩
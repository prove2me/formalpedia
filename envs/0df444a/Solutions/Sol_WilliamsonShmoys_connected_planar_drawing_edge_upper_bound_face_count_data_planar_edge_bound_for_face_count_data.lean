-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_drawing_edge_upper_bound_face_count_data_planar_edge_bound_for_face_count_data
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T10:27:43.452618+00:00
-- url     : https://prove2.me/submissions/908253fd-d089-4b3f-ab0d-2826cd43c632
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_euler_face_data

set_option autoImplicit false
open scoped BigOperators

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hconn : K.Connected) :
    K.edgeSet.ncard <= 3 * Fintype.card V - 6 := by
  obtain ⟨f, boundaryLength, hEuler, hBoundarySum, hBoundaryLower⟩ :=
    WilliamsonShmoys.connected_planar_drawing_euler_face_data K hV hK hconn
  have hFaceBound : 3 * f <= 2 * K.edgeSet.ncard := by
    calc
      3 * f = ∑ i : Fin f, 3 := by simp; omega
      _ <= ∑ i : Fin f, boundaryLength i := Finset.sum_le_sum (by
        intro i hi
        exact hBoundaryLower i)
      _ = 2 * K.edgeSet.ncard := hBoundarySum
  omega
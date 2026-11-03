-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_connected_edge_bound__p2m_fab89fb1_e873_4b82_98f3_cd1985d7426b_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T17:41:43.839256+00:00
-- url     : https://prove2.me/submissions/470a2060-88f6-44d2-9b30-73099d94f635

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_face_count_certificate__p2m_84071c7f_05d0_4d93_a512_f7a4506c6617_a1
import Mathlib

set_option autoImplicit false
open WilliamsonShmoys
open scoped BigOperators

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hConnected : K.Connected)
    (hPlanar : HasPlanarDrawingOn K) :
    letI : DecidableRel K.Adj := Classical.decRel K.Adj
    K.edgeFinset.card + 6 <= 3 * Fintype.card V := by
  classical
  letI : DecidableRel K.Adj := Classical.decRel K.Adj
  rcases WilliamsonShmoys.planar_drawing_face_count_certificate__p2m_84071c7f_05d0_4d93_a512_f7a4506c6617_a1
      K hConnected hPlanar with htree | ⟨f, boundaryLength, hEuler, hPerimeter, hFace⟩
  · omega
  · have hLower :
        3 * f <= ∑ i : Fin f, boundaryLength i := by
      calc
        3 * f = f * 3 := Nat.mul_comm _ _
        _ = ∑ _i : Fin f, 3 := by simp
        _ <= ∑ i : Fin f, boundaryLength i :=
          Finset.sum_le_sum fun i hi => hFace i
    have hFaces : 3 * f <= 2 * K.edgeFinset.card := by
      rw [hPerimeter] at hLower
      exact hLower
    omega
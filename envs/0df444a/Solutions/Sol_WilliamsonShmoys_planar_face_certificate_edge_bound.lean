-- Prove2me | solution 1 for WilliamsonShmoys.planar_face_certificate_edge_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T23:27:32.699625+00:00
-- url     : https://prove2.me/submissions/fcc6cde4-a171-4c3f-a1ca-aebc609f9c31

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V]
    (K : SimpleGraph V)
    (faceCount : ℕ)
    (boundaryLength : Fin faceCount → ℕ)
    (hEuler : Fintype.card V + faceCount = K.edgeSet.ncard + 2)
    (hIncidence : (∑ i : Fin faceCount, boundaryLength i) = 2 * K.edgeSet.ncard)
    (hBoundary : ∀ i : Fin faceCount, 3 ≤ boundaryLength i) :
    K.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  have hsum :
      (∑ i : Fin faceCount, 3) ≤ ∑ i : Fin faceCount, boundaryLength i := by
    apply Finset.sum_le_sum
    intro i hi
    exact hBoundary i
  have hfaces : 3 * faceCount ≤ 2 * K.edgeSet.ncard := by
    calc
      3 * faceCount = ∑ i : Fin faceCount, 3 := by simp [Nat.mul_comm]
      _ ≤ ∑ i : Fin faceCount, boundaryLength i := hsum
      _ = 2 * K.edgeSet.ncard := hIncidence
  omega

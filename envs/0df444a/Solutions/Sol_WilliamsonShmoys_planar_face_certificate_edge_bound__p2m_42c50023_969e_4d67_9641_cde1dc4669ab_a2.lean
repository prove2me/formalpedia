-- Prove2me | solution 1 for WilliamsonShmoys.planar_face_certificate_edge_bound__p2m_42c50023_969e_4d67_9641_cde1dc4669ab_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:17:12.121872+00:00
-- url     : https://prove2.me/submissions/6da84c60-8710-4d46-9a1b-be4605f49ea9

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (faceCount : Nat)
    (hcard : 3 ≤ Fintype.card V)
    (hboundary : ∃ boundaryLength : Fin faceCount → Nat,
      (∑ f : Fin faceCount, boundaryLength f) = 2 * K.edgeFinset.card ∧
      (∀ f : Fin faceCount, 3 ≤ boundaryLength f))
    (heuler : Fintype.card V + faceCount = K.edgeFinset.card + 2) :
    K.edgeFinset.card ≤ 3 * Fintype.card V - 6 := by
  rcases hboundary with ⟨boundaryLength, hsum, hface⟩
  have hfaces : 3 * faceCount ≤ ∑ f : Fin faceCount, boundaryLength f := by
    calc
      3 * faceCount = ∑ f : Fin faceCount, 3 := by simp [Nat.mul_comm]
      _ ≤ ∑ f : Fin faceCount, boundaryLength f :=
        Finset.sum_le_sum (fun f _ => hface f)
  omega
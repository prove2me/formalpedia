-- Prove2me | solution 1 for WilliamsonShmoys.euler_face_data_edge_bound__p2m_55f47020_da90_4034_b4af_759a470f5d81_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T06:57:54.004211+00:00
-- url     : https://prove2.me/submissions/0e66dcac-5b11-4dd5-8423-9cc1ad36ace6

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (faceCount : Nat)
    (boundaryLength : Fin faceCount → Nat)
    (hEuler : faceCount + Fintype.card V = G.edgeFinset.card + 2)
    (hIncidence : (∑ f : Fin faceCount, boundaryLength f) = 2 * G.edgeFinset.card)
    (hLength : ∀ f, 3 ≤ boundaryLength f)
    (hcard : 3 ≤ Fintype.card V) :
    G.edgeFinset.card ≤ 3 * Fintype.card V - 6 := by
  have hsum : 3 * faceCount ≤ ∑ f : Fin faceCount, boundaryLength f := by
    calc
      3 * faceCount = ∑ _f : Fin faceCount, 3 := by simp <;> omega
      _ ≤ ∑ f : Fin faceCount, boundaryLength f :=
        Finset.sum_le_sum (fun f _ => hLength f)
  omega
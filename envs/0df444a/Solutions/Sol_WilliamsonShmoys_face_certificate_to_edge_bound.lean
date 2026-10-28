-- Prove2me | solution 1 for WilliamsonShmoys.face_certificate_to_edge_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T23:40:29.653635+00:00
-- url     : https://prove2.me/submissions/77de8ccd-147c-4a69-8acb-13917f50e22f

import Mathlib

set_option autoImplicit false
open scoped BigOperators

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (F : ℕ)
    (faceLength : Fin F → ℕ)
    (hF : 0 < F)
    (hEuler : Fintype.card V + F = L.edgeSet.ncard + 2)
    (hIncidences : (∑ i : Fin F, faceLength i) = 2 * L.edgeSet.ncard)
    (hFaceLength : ∀ i, 3 ≤ faceLength i)
    (hV : 3 ≤ Fintype.card V) :
    L.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  have h : ∑ _i : Fin F, 3 ≤ ∑ i : Fin F, faceLength i :=
    Finset.sum_le_sum fun i _ => hFaceLength i
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h
  omega

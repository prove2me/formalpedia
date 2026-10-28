-- Prove2me | solution 1 for WilliamsonShmoys.face_certificate_edge_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T09:26:35.221906+00:00
-- url     : https://prove2.me/submissions/186abed2-7e4d-4403-99cf-379956ab1786

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V]
    (K : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (m : Nat) (degree : Fin m -> Int)
    (heuler : (Fintype.card V : Int) - (K.edgeSet.ncard : Int) + m = 2)
    (hincidence : (∑ f : Fin m, degree f) = 2 * (K.edgeSet.ncard : Int))
    (hdegree : ∀ f, 3 <= degree f) :
    K.edgeSet.ncard + 6 <= 3 * Fintype.card V := by
  have hsum : (∑ f : Fin m, (3 : Int)) <= ∑ f : Fin m, degree f := by
    apply Finset.sum_le_sum
    intro f hf
    exact hdegree f
  have hfaces : (m : Int) * 3 <= 2 * (K.edgeSet.ncard : Int) := by
    simpa using hsum.trans (le_of_eq hincidence)
  omega
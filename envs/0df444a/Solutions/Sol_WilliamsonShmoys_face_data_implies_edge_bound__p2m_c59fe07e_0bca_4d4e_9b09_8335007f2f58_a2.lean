-- Prove2me | solution 1 for WilliamsonShmoys_face_data_implies_edge_bound__p2m_c59fe07e_0bca_4d4e_9b09_8335007f2f58_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:19:08.297475+00:00
-- url     : https://prove2.me/submissions/26205ef4-796c-4b78-abae-e543f70f1eed

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hdata : ∃ f : ℕ,
      (Fintype.card V : ℤ) - (K.edgeSet.ncard : ℤ) + (f : ℤ) = 2 ∧
      (3 : ℤ) * (f : ℤ) ≤ 2 * (K.edgeSet.ncard : ℤ)) :
    K.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  obtain ⟨f, heuler, hfaces⟩ := hdata
  omega
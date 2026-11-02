-- Prove2me | solution 1 for WilliamsonShmoys.planar_face_count_certificate_edge_bound__p2m_8c314bc4_0fdc_4634_a839_40069b48478f_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T06:47:20.751094+00:00
-- url     : https://prove2.me/submissions/0e0f58d0-e2a7-472e-83c5-b645374bc6e5

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V)
    (F : ℕ) :
    letI : DecidableRel P.Adj := Classical.decRel P.Adj
    (Fintype.card V + F = P.edgeFinset.card + 2) ->
    (3 * F = 2 * P.edgeFinset.card) ->
    (3 <= Fintype.card V) ->
    3 * Fintype.card V - 6 <= P.edgeFinset.card := by
  intro hEuler hInc hV
  omega
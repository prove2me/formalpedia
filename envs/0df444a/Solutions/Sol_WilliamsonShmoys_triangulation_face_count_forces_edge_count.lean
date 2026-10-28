-- Prove2me | solution 1 for WilliamsonShmoys.triangulation_face_count_forces_edge_count
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T13:35:22.386071+00:00
-- url     : https://prove2.me/submissions/3cc66ce9-69a6-49ff-b416-75a45ace5717

import Mathlib

set_option autoImplicit false

theorem solution
    {n e : ℕ} {F : Type} [Fintype F]
    (boundaryLength : F → ℕ)
    (hEuler : n + Fintype.card F = e + 2)
    (hIncidence : (∑ f : F, boundaryLength f) = 2 * e)
    (hTriangle : ∀ f, boundaryLength f = 3) :
    3 * n = e + 6 := by
  have hFaces : Fintype.card F * 3 = 2 * e := by
    simpa [hTriangle] using hIncidence
  omega
-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count_for_face_equations
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T05:28:17.011918+00:00
-- url     : https://prove2.me/submissions/87fe09c1-4998-40cc-a167-903aabb278de

import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_face_equations_for_edge_count_9ae33b99_f9c7_42b4_990c_c6c34d566138

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : HasPlanarDrawingOn M)
    (hMax : ∀ H : SimpleGraph V, M ≤ H → HasPlanarDrawingOn H → H = M)
    (hCard : 3 ≤ Fintype.card V) :
    M.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨f, hEuler, hIncidence⟩ :=
    WilliamsonShmoys.maximal_planar_drawing_face_equations_for_edge_count_9ae33b99_f9c7_42b4_990c_c6c34d566138
      M hM hMax hCard
  omega
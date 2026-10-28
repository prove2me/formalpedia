-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_lower_bound_face_equations_9ae33b99
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T06:24:12.562143+00:00
-- url     : https://prove2.me/submissions/c68a8f99-2e4c-4bd8-b5ef-9ac601fecfa6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_WilliamsonShmoys_maximal_planar_face_equations_for_edge_lower_bound_9ae33b99

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : HasPlanarDrawingOn L)
    (hMax : ∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M = L)
    (hCard : 3 ≤ Fintype.card V) :
    3 * Fintype.card V - 6 ≤ L.edgeSet.ncard := by
  obtain ⟨f, hEuler, hFaceIncidence⟩ :=
    WilliamsonShmoys.maximal_planar_face_equations_for_edge_lower_bound_9ae33b99
      L hL hMax hCard
  omega
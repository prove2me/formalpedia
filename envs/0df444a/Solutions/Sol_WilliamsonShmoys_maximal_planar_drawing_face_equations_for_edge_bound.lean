-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_face_equations_for_edge_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T05:04:38.497059+00:00
-- url     : https://prove2.me/submissions/a6f46e8c-fc99-43b5-bbd1-6f79b5089d90
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_for_face_equations

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : HasPlanarDrawingOn M)
    (hMax : ∀ H : SimpleGraph V, M ≤ H → HasPlanarDrawingOn H → H = M)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ f : ℕ,
      Fintype.card V + f = M.edgeSet.ncard + 2 ∧
      3 * f = 2 * M.edgeSet.ncard := by
  have hE := WilliamsonShmoys.maximal_planar_drawing_edge_count_for_face_equations
    M hM hMax hCard
  refine ⟨2 * Fintype.card V - 4, ?_, ?_⟩ <;> omega
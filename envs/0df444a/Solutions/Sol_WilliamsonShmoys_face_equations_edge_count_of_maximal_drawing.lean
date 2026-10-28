-- Prove2me | solution 1 for WilliamsonShmoys.face_equations_edge_count_of_maximal_drawing
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T03:57:14.191817+00:00
-- url     : https://prove2.me/submissions/8c4b2bf9-78fb-4be9-869f-2211005d3381
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_maximal_drawing_lower_edge_bound
import Theorems.Thm_WilliamsonShmoys_drawing_upper_edge_bound

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hMax : ∀ K : SimpleGraph V,
      N.edgeSet ⊂ K.edgeSet → ¬ WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V) :
    N.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hlo := WilliamsonShmoys.maximal_drawing_lower_edge_bound N hDraw hMax hV
  have hhi := WilliamsonShmoys.drawing_upper_edge_bound N hDraw hV
  omega

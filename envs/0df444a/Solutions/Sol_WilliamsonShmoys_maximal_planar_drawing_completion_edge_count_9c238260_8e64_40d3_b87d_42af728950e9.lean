-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_completion_edge_count_9c238260_8e64_40d3_b87d_42af728950e9
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T05:43:02.166037+00:00
-- url     : https://prove2.me/submissions/925d4c8a-be73-4e47-a675-be83a977886e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_completion_edge_count_9c238260_8e64_40d3_b87d_42af728950e9_planar_edge_upper_bound
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_completion_edge_count_9c238260_8e64_40d3_b87d_42af728950e9_maximal_edge_lower_bound
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hDrawing : HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V)
    (hMaximal : ∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K ≤ H) :
    H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hUpper := WilliamsonShmoys.maximal_planar_drawing_completion_edge_count_9c238260_8e64_40d3_b87d_42af728950e9_planar_edge_upper_bound
    H hDrawing hV
  have hLower := WilliamsonShmoys.maximal_planar_drawing_completion_edge_count_9c238260_8e64_40d3_b87d_42af728950e9_maximal_edge_lower_bound
    H hDrawing hV hMaximal
  omega
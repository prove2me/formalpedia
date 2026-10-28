-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count_9ddd260a_fbe4_4ded_ae27_61e055e9256a
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T05:52:43.172328+00:00
-- url     : https://prove2.me/submissions/7158e30f-5e9e-4878-bc19-e339baca3b87
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_upper_bound
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_lower_bound

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hDrawing : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hMaximal : ∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H)
    (hV : 3 ≤ Fintype.card V) :
    3 * Fintype.card V = H.edgeSet.ncard + 6 := by
  have hUpper := WilliamsonShmoys.maximal_planar_drawing_edge_count_upper_bound H hDrawing hV
  have hLower := WilliamsonShmoys.maximal_planar_drawing_edge_count_lower_bound H hDrawing hMaximal hV
  omega
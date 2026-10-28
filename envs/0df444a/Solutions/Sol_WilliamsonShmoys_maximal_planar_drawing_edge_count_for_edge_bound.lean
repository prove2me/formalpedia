-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count_for_edge_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T02:20:58.158112+00:00
-- url     : https://prove2.me/submissions/36af11b6-93ba-412d-8877-e4bbe785712b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_edge_count_upper_bound_from_drawing_e3d40089
import Theorems.Thm_WilliamsonShmoys_maximal_edge_count_lower_bound_from_drawing_e3d40089

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hcard : 3 <= Fintype.card V)
    (hmax : ∀ K : SimpleGraph V, G ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = G) :
    G.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hupper := WilliamsonShmoys.edge_count_upper_bound_from_drawing_e3d40089 G hG hcard
  have hlower := WilliamsonShmoys.maximal_edge_count_lower_bound_from_drawing_e3d40089 G hG hcard hmax
  omega

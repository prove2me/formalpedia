-- Prove2me | solution 1 for WilliamsonShmoys.edge_count_upper_bound_of_maximal_planar_drawing__p2m_0ef6cdd6_0074_4ddf_9918_5e48acac88b4_a3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T23:14:46.451096+00:00
-- url     : https://prove2.me/submissions/fd65f6f4-b546-4dec-956b-2599e15b26d1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_count_upper_bound__p2m_38a90fc3_dea3_4c9f_8a52_b5002f138593_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hmax : ∀ K : SimpleGraph V,
      G ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = G) :
    G.edgeSet.ncard + 6 <= 3 * Fintype.card V := by
  exact WilliamsonShmoys.planar_drawing_edge_count_upper_bound__p2m_38a90fc3_dea3_4c9f_8a52_b5002f138593_a1
    G hV hG
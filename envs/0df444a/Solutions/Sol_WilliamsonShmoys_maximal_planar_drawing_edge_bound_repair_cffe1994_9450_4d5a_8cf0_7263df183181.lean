-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_bound_repair_cffe1994_9450_4d5a_8cf0_7263df183181
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T00:25:55.651995+00:00
-- url     : https://prove2.me/submissions/0a808cf4-f58c-44b4-8e53-18a4f75fb21e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_graph_edge_bound

set_option autoImplicit false

 theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hmax : forall N : SimpleGraph V,
      M <= N ->
      WilliamsonShmoys.HasPlanarDrawingOn N ->
      N = M) :
    3 * Fintype.card V - 6 <= M.edgeSet.ncard := by
  exact WilliamsonShmoys.planar_graph_edge_bound M hV hM
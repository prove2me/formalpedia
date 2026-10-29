-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_supergraph_edge_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T00:20:47.635654+00:00
-- url     : https://prove2.me/submissions/00a39361-862a-4abd-bf08-f04a9b8ebdf4

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_finite_maximal_supergraph_cffe1994_9450_4d5a_8cf0_7263df183181
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_bound_repair_cffe1994_9450_4d5a_8cf0_7263df183181

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    Exists fun M : SimpleGraph V =>
      G <= M /\
      WilliamsonShmoys.HasPlanarDrawingOn M /\
      3 * Fintype.card V - 6 <= M.edgeSet.ncard := by
  exact Exists.elim
    (WilliamsonShmoys.planar_drawing_finite_maximal_supergraph_cffe1994_9450_4d5a_8cf0_7263df183181
      G hV hG)
    (fun M h => Exists.intro M
      (And.intro h.1
        (And.intro h.2.1
          (WilliamsonShmoys.maximal_planar_drawing_edge_bound_repair_cffe1994_9450_4d5a_8cf0_7263df183181
            M hV h.2.1 h.2.2))))
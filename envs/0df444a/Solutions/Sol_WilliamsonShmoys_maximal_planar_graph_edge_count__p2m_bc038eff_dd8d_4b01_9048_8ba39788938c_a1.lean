-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_bc038eff_dd8d_4b01_9048_8ba39788938c_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:42:09.481442+00:00
-- url     : https://prove2.me/submissions/da8afb59-72ae-4fe3-930f-46028569e2b5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_upper_bound__p2m_1a017428_1a43_436d_9208_530136878881_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_lower_edge_count__p2m_1a017428_1a43_436d_9208_530136878881_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hcard : 3 <= Fintype.card V)
    (hmax : forall M : SimpleGraph V,
      (forall {u v : V}, L.Adj u v -> M.Adj u v) ->
      WilliamsonShmoys.HasPlanarDrawingOn M ->
      (forall {u v : V}, M.Adj u v -> L.Adj u v)) :
    (letI : DecidableRel L.Adj := Classical.decRel L.Adj
     L.edgeFinset.card = 3 * Fintype.card V - 6) := by
  have hupper := WilliamsonShmoys.planar_drawing_edge_upper_bound__p2m_1a017428_1a43_436d_9208_530136878881_a1
    L hL hcard
  have hlower := WilliamsonShmoys.maximal_planar_lower_edge_count__p2m_1a017428_1a43_436d_9208_530136878881_a1
    L hL hcard hmax
  omega
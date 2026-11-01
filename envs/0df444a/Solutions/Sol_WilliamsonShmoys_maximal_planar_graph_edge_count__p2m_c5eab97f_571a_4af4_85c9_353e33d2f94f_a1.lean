-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_c5eab97f_571a_4af4_85c9_353e33d2f94f_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T03:19:44.625193+00:00
-- url     : https://prove2.me/submissions/bf603f09-5cc7-4955-aeae-d87051b6f39d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_upper_bound__p2m_438c2037_6b64_401b_a3fa_84e1ccf42d6c_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_simple_graph_edge_lower_bound__p2m_438c2037_6b64_401b_a3fa_84e1ccf42d6c_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ K' : SimpleGraph V, K ≤ K' →
      WilliamsonShmoys.HasPlanarDrawingOn K' → K' = K) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hupper := WilliamsonShmoys.planar_simple_graph_edge_upper_bound__p2m_438c2037_6b64_401b_a3fa_84e1ccf42d6c_a1 K hK hcard
  have hlower := WilliamsonShmoys.maximal_planar_simple_graph_edge_lower_bound__p2m_438c2037_6b64_401b_a3fa_84e1ccf42d6c_a1 K hK hcard hmax
  omega
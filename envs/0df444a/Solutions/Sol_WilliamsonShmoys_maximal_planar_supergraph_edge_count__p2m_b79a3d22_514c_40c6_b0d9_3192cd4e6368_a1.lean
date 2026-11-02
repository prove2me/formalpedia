-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_supergraph_edge_count__p2m_b79a3d22_514c_40c6_b0d9_3192cd4e6368_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T13:03:58.363653+00:00
-- url     : https://prove2.me/submissions/05d99151-375f-4fda-8a93-77a613f0a9cf
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper__p2m_23689463_5c07_4e0b_a29b_546de8e1e4a9_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower__p2m_23689463_5c07_4e0b_a29b_546de8e1e4a9_a1

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (dL : DecidableRel L.Adj)
    (hL : HasPlanarDrawingOn L) (hcard : 3 <= Fintype.card V)
    (hmax : forall (M : SimpleGraph V) (dM : DecidableRel M.Adj),
      L <= M -> HasPlanarDrawingOn M -> M <= L) :
    3 * Fintype.card V = L.edgeFinset.card + 6 := by
  have hupper := WilliamsonShmoys.planar_edge_count_upper__p2m_23689463_5c07_4e0b_a29b_546de8e1e4a9_a1
    L dL hL hcard
  have hlower := WilliamsonShmoys.maximal_planar_edge_count_lower__p2m_23689463_5c07_4e0b_a29b_546de8e1e4a9_a1
    L dL hL hcard hmax
  omega
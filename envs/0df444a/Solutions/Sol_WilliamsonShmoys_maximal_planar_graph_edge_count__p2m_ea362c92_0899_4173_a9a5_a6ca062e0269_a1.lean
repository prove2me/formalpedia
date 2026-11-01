-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_ea362c92_0899_4173_a9a5_a6ca062e0269_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:09:12.444581+00:00
-- url     : https://prove2.me/submissions/0c702aab-d790-44a2-a8df-7240959cdc28
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_upper_bound__p2m_1df68e30_02cf_4572_bf8a_d78917d2b48a_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound__p2m_1df68e30_02cf_4572_bf8a_d78917d2b48a_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hmax : ∀ K : SimpleGraph V, L ≤ K →
      WilliamsonShmoys.HasPlanarDrawingOn K → K = L) :
    L.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  have hu :=
    WilliamsonShmoys.planar_drawing_edge_upper_bound__p2m_1df68e30_02cf_4572_bf8a_d78917d2b48a_a1
      L hcard hL
  have hl :=
    WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_1df68e30_02cf_4572_bf8a_d78917d2b48a_a1
      L hcard hL hmax
  omega
-- Prove2me | solution 1 for WilliamsonShmoys.edge_maximal_planar_edge_count__p2m_9aae8c1a_0088_4039_a6d9_b99fa0bd700a_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T16:46:58.118286+00:00
-- url     : https://prove2.me/submissions/09c48096-ef4a-404c-9d3e-dec2b8f4b328
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_edge_maximal_planar_edge_lower_bound__p2m_2a34f2f7_4575_4fc5_979a_579be47b545a_a1
import Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_upper_bound__p2m_2a34f2f7_4575_4fc5_979a_579be47b545a_a1
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ K : SimpleGraph V,
      N ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = N) :
    N.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  have h_lower := WilliamsonShmoys.edge_maximal_planar_edge_lower_bound__p2m_2a34f2f7_4575_4fc5_979a_579be47b545a_a1 N hN hcard hmax
  have h_upper := WilliamsonShmoys.planar_simple_graph_edge_upper_bound__p2m_2a34f2f7_4575_4fc5_979a_579be47b545a_a1 N hN hcard
  omega
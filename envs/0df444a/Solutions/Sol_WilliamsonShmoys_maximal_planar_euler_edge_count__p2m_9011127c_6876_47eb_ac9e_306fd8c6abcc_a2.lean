-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_euler_edge_count__p2m_9011127c_6876_47eb_ac9e_306fd8c6abcc_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T10:03:43.582479+00:00
-- url     : https://prove2.me/submissions/b0a86f01-3645-427d-b2e2-456b302996ed
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_upper_bound__p2m_5de67bd5_1b50_462c_9c5e_b0f0f644e7f0_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound__p2m_5de67bd5_1b50_462c_9c5e_b0f0f644e7f0_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hcard : 3 ≤ (Set.univ : Set V).ncard)
    (hMax : ∀ P : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn P →
      N.edgeSet ⊆ P.edgeSet → P.edgeSet ⊆ N.edgeSet) :
    N.edgeSet.ncard + 6 = 3 * (Set.univ : Set V).ncard := by
  have hUpper := WilliamsonShmoys.planar_simple_graph_edge_upper_bound__p2m_5de67bd5_1b50_462c_9c5e_b0f0f644e7f0_a1 N hDraw hcard
  have hLower := WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_5de67bd5_1b50_462c_9c5e_b0f0f644e7f0_a1 N hDraw hcard hMax
  omega
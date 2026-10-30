-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_edge_count_2e173d6b
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T05:52:25.222841+00:00
-- url     : https://prove2.me/submissions/18d38371-d5f2-49af-8357-17a518ba9c26

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_upper_bound_c5c6f6ee
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound_c5c6f6ee

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hmax : ∀ N : SimpleGraph V, M ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N → N = M) :
    M.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hup := WilliamsonShmoys.planar_edge_upper_bound_c5c6f6ee M hV hM
  have hlo := WilliamsonShmoys.maximal_planar_edge_lower_bound_c5c6f6ee M hV hM hmax
  omega
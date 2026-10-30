-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_c28c5998_faac_44a3_b6f1_2a93fc56a9eb_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:13:58.547311+00:00
-- url     : https://prove2.me/submissions/6db0e3e6-4edd-4893-8eda-30904c429b54
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_upper_bound__p2m_94c3c327_8601_4c2d_adbc_08897459bc6e_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_simple_graph_edge_lower_bound__p2m_94c3c327_8601_4c2d_adbc_08897459bc6e_a1
open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V) (hG : HasPlanarDrawingOn G)
    (hmax : ∀ K : SimpleGraph V, G ≤ K → HasPlanarDrawingOn K → K = G) :
    G.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hUpper := WilliamsonShmoys.planar_simple_graph_edge_upper_bound__p2m_94c3c327_8601_4c2d_adbc_08897459bc6e_a1 G hV hG
  have hLower := WilliamsonShmoys.maximal_planar_simple_graph_edge_lower_bound__p2m_94c3c327_8601_4c2d_adbc_08897459bc6e_a1 G hV hG hmax
  omega
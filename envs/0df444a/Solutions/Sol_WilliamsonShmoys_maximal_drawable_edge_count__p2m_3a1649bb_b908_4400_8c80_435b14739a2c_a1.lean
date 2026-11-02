-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_edge_count__p2m_3a1649bb_b908_4400_8c80_435b14739a2c_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T16:16:00.980568+00:00
-- url     : https://prove2.me/submissions/c8532428-0191-4c61-abef-b696e206493c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_bound__p2m_319863c5_d9cf_422f_8cc1_e579df5fd0de_a2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_lower_bound__p2m_319863c5_d9cf_422f_8cc1_e579df5fd0de_a2
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hMax : ∀ L : SimpleGraph V,
      M.edgeSet ⊆ L.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn L →
      M.edgeSet = L.edgeSet) :
    M.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  have hUpper := WilliamsonShmoys.planar_simple_graph_edge_bound__p2m_319863c5_d9cf_422f_8cc1_e579df5fd0de_a2 M hCard hM
  have hLower := WilliamsonShmoys.maximal_planar_graph_edge_lower_bound__p2m_319863c5_d9cf_422f_8cc1_e579df5fd0de_a2 M hCard hM hMax
  omega
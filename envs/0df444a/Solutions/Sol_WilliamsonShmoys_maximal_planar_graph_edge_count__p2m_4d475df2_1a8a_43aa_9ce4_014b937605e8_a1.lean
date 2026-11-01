-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_4d475df2_1a8a_43aa_9ce4_014b937605e8_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:56:11.216408+00:00
-- url     : https://prove2.me/submissions/a0638af1-47cb-4b6f-b339-ebde38160252

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_bound__p2m_04b260ca_6bc4_40b7_9582_99be510cc2b0_a3
import Theorems.Thm_WilliamsonShmoys_maximal_planar_simple_graph_edge_lower_bound__p2m_04b260ca_6bc4_40b7_9582_99be510cc2b0_a3
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V,
      H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ H) :
    3 * Fintype.card V = H.edgeSet.ncard + 6 := by
  have hupper :=
    WilliamsonShmoys.planar_simple_graph_edge_bound__p2m_04b260ca_6bc4_40b7_9582_99be510cc2b0_a3
      H hcard hH
  have hlower :=
    WilliamsonShmoys.maximal_planar_simple_graph_edge_lower_bound__p2m_04b260ca_6bc4_40b7_9582_99be510cc2b0_a3
      H hcard hH hmax
  omega
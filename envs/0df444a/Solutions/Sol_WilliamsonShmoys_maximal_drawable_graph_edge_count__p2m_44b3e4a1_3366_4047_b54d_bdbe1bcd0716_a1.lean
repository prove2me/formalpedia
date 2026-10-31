-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_graph_edge_count__p2m_44b3e4a1_3366_4047_b54d_bdbe1bcd0716_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T06:20:21.148967+00:00
-- url     : https://prove2.me/submissions/402c3a7a-a172-4f6e-9487-71eaa8a34480

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_upper_bound__p2m_7d768a9f_2454_410a_aba4_32911cd0fa44_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound__p2m_7d768a9f_2454_410a_aba4_32911cd0fa44_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H)
    (hV : 3 ≤ Fintype.card V) :
    H.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  have hup := WilliamsonShmoys.planar_edge_upper_bound__p2m_7d768a9f_2454_410a_aba4_32911cd0fa44_a1 H hH hV
  have hlo := WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_7d768a9f_2454_410a_aba4_32911cd0fa44_a1 H hH hmax hV
  omega
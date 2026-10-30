-- Prove2me | solution 1 for WilliamsonShmoys.planar_graph_edge_count_upper_bound__p2m_7ed45ce9_fab7_4799_9a3a_4afc5611b50c_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:53:15.072882+00:00
-- url     : https://prove2.me/submissions/dc48a09d-be8a-4def-a83d-dcac964f5ff3

import Theorems.Thm_WilliamsonShmoys_planar_triangulation_supergraph_edge_bound__p2m_d62f521f_25cd_4ab7_9962_c745608392d5_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hDraw : HasPlanarDrawingOn N)
    (hV : 3 ≤ Fintype.card V) :
    N.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨H, hNH, hDrawH, hCard, hExact⟩ :=
    WilliamsonShmoys.planar_triangulation_supergraph_edge_bound__p2m_d62f521f_25cd_4ab7_9962_c745608392d5_a1
      N hDraw hV
  omega
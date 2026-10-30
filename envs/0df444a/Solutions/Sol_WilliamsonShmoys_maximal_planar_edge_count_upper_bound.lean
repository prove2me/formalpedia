-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_upper_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T09:13:03.989644+00:00
-- url     : https://prove2.me/submissions/d60edada-13b0-49d1-b225-10b520c4865a

import Theorems.Thm_WilliamsonShmoys_planar_edge_bound_extension_to_maximal
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_has_exact_edge_count_v2

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V) :
    L.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  obtain ⟨H, hLH, hH, hMax, hEdges⟩ :=
    WilliamsonShmoys.planar_edge_bound_extension_to_maximal L hL hCard
  have hExact :=
    WilliamsonShmoys.maximal_planar_graph_has_exact_edge_count_v2 H hH hMax hCard
  omega
-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_upper_bound_for_maximal_planar_edge_count_by_triangulation_65d9599f
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T03:07:57.865747+00:00
-- url     : https://prove2.me/submissions/2a06af56-f37f-4f30-af00-896f51eed1bd

import Theorems.Thm_WilliamsonShmoys_planar_supergraph_triangulation_for_edge_bound
import Theorems.Thm_WilliamsonShmoys_edge_count_mono_of_subgraph

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨K, hHK, hK, hEq⟩ :=
    WilliamsonShmoys.planar_supergraph_triangulation_for_edge_bound H hV hH
  have hle := WilliamsonShmoys.edge_count_mono_of_subgraph H K hHK
  omega
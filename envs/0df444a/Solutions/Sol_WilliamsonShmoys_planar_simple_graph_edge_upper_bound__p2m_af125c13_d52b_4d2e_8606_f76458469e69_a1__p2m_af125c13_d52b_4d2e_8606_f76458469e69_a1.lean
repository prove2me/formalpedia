-- Prove2me | solution 1 for WilliamsonShmoys.planar_simple_graph_edge_upper_bound__p2m_af125c13_d52b_4d2e_8606_f76458469e69_a1__p2m_af125c13_d52b_4d2e_8606_f76458469e69_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T01:59:39.613893+00:00
-- url     : https://prove2.me/submissions/ea3e2646-9716-426e-b89c-3491fb8ae65c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_connected_planar_component_edge_bound__p2m_af6b56d0_9fee_4e0d_9b9d_0f9d0aadcf1d_a2
import Theorems.Thm_WilliamsonShmoys_planar_connected_component_partition__p2m_af6b56d0_9fee_4e0d_9b9d_0f9d0aadcf1d_a2
import Theorems.Thm_WilliamsonShmoys_planar_component_edge_count_aggregation__p2m_af6b56d0_9fee_4e0d_9b9d_0f9d0aadcf1d_a2

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hplanar : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hcard : 3 ≤ Fintype.card V) :
    M.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨parts, hcover, hnonempty, hdisjoint, hadj, hconn, hdraw⟩ :=
    WilliamsonShmoys.planar_connected_component_partition__p2m_af6b56d0_9fee_4e0d_9b9d_0f9d0aadcf1d_a2
      M hplanar
  exact WilliamsonShmoys.planar_component_edge_count_aggregation__p2m_af6b56d0_9fee_4e0d_9b9d_0f9d0aadcf1d_a2
    M parts hcover hnonempty hdisjoint hadj hconn hdraw
    (fun C hC hCcard =>
      WilliamsonShmoys.connected_planar_component_edge_bound__p2m_af6b56d0_9fee_4e0d_9b9d_0f9d0aadcf1d_a2
        (M.induce (C : Set V)) (hdraw C hC) (hconn C hC) hCcard)
    hcard
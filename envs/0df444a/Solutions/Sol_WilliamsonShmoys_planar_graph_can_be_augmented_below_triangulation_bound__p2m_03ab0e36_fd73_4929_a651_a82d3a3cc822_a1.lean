-- Prove2me | solution 1 for WilliamsonShmoys.planar_graph_can_be_augmented_below_triangulation_bound__p2m_03ab0e36_fd73_4929_a651_a82d3a3cc822_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T20:17:45.866995+00:00
-- url     : https://prove2.me/submissions/02267afb-1379-4204-b7c5-3b8a668f26b3

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph_exists__p2m_b3d3d4e0_653c_48d5_a9c6_646106519c2d_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_bound__p2m_b3d3d4e0_653c_48d5_a9c6_646106519c2d_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hM : HasPlanarDrawingOn M)
    (hcount : M.edgeSet.ncard < 3 * Fintype.card V - 6) :
    ∃ N : SimpleGraph V, M ≤ N ∧ N ≠ M ∧ HasPlanarDrawingOn N := by
  obtain ⟨N, hMN, hN, hmax⟩ :=
    WilliamsonShmoys.maximal_planar_supergraph_exists__p2m_b3d3d4e0_653c_48d5_a9c6_646106519c2d_a1 M hM
  have hbound :=
    WilliamsonShmoys.maximal_planar_graph_edge_bound__p2m_b3d3d4e0_653c_48d5_a9c6_646106519c2d_a1 N hV hN hmax
  have hlt : M.edgeSet.ncard < N.edgeSet.ncard := lt_of_lt_of_le hcount hbound
  have hcard : M.edgeSet.ncard ≤ N.edgeSet.ncard :=
    Set.ncard_le_ncard (SimpleGraph.edgeSet_mono hMN)
  have hneq : N ≠ M := by
    intro heq
    subst N
    omega
  exact ⟨N, hMN, hneq, hN⟩
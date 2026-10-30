-- Prove2me | solution 1 for WilliamsonShmoys.exists_planar_triangulation_supergraph_4a969e66
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T10:41:12.120708+00:00
-- url     : https://prove2.me/submissions/7c3fa3a7-3d3b-4ec7-9dc7-1df650519da4

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_edge_maximal_planar_supergraph_on
import Theorems.Thm_WilliamsonShmoys_edge_count_of_edge_maximal_planar_graph_on

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ N : SimpleGraph V,
      M ≤ N ∧
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      N.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨N, hMN, hN, hMax⟩ :=
    WilliamsonShmoys.exists_edge_maximal_planar_supergraph_on M hM
  have hCount :=
    WilliamsonShmoys.edge_count_of_edge_maximal_planar_graph_on N hN hCard hMax
  exact ⟨N, hMN, hN, hCount⟩
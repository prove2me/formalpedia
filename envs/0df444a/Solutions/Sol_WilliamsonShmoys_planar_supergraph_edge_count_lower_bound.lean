-- Prove2me | solution 1 for WilliamsonShmoys.planar_supergraph_edge_count_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T08:15:55.115772+00:00
-- url     : https://prove2.me/submissions/e8b92c47-d257-4bd1-a4a7-dfa458d20d20

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_exists_edge_maximal_v2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count_v2

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hP : WilliamsonShmoys.HasPlanarDrawingOn P) :
    ∃ Q : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn Q ∧
      Set.Subset P.edgeSet Q.edgeSet ∧
      3 * Fintype.card V ≤ Q.edgeSet.ncard + 6 := by
  obtain ⟨Q, hQ, hPQ, hmax⟩ :=
    WilliamsonShmoys.planar_supergraph_exists_edge_maximal_v2 P hP
  have hbound :=
    WilliamsonShmoys.maximal_planar_graph_edge_count_v2 Q hCard hQ hmax
  exact ⟨Q, hQ, hPQ, hbound⟩
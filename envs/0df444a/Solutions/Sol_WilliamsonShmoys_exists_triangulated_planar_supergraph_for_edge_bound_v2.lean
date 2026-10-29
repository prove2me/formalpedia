-- Prove2me | solution 1 for WilliamsonShmoys.exists_triangulated_planar_supergraph_for_edge_bound_v2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T19:49:22.743623+00:00
-- url     : https://prove2.me/submissions/dd88994e-1ff3-4385-af6a-0f3ce7fb48f7

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_edge_maximal_planar_supergraph_v2
import Theorems.Thm_WilliamsonShmoys_edge_maximal_planar_edge_count_v2

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hPdraw : WilliamsonShmoys.HasPlanarDrawingOn P) :
    ∃ Q : SimpleGraph V,
      P ≤ Q ∧ WilliamsonShmoys.HasPlanarDrawingOn Q ∧
        Q.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨Q, hPQ, hQdraw, hmax⟩ :=
    WilliamsonShmoys.exists_edge_maximal_planar_supergraph_v2 P hPdraw
  exact ⟨Q, hPQ, hQdraw,
    WilliamsonShmoys.edge_maximal_planar_edge_count_v2 Q hV hQdraw hmax⟩
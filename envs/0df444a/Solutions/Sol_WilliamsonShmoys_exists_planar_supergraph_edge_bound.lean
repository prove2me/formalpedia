-- Prove2me | solution 1 for WilliamsonShmoys.exists_planar_supergraph_edge_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T18:40:38.100447+00:00
-- url     : https://prove2.me/submissions/84661295-fdfb-42ac-880a-f6afa2124686

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_finite_choice
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_bound_from_drawing

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hMdraw : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V, M ≤ N ∧
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      3 * Fintype.card V - 6 ≤ N.edgeSet.ncard := by
  obtain ⟨N, hMN, hNdraw, hNmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph_finite_choice M hMdraw
  have hbound :=
    WilliamsonShmoys.maximal_planar_edge_bound_from_drawing N hV hNdraw hNmax
  exact ⟨N, hMN, hNdraw, hbound⟩
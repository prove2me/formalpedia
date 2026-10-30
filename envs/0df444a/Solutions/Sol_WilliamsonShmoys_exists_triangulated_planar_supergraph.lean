-- Prove2me | solution 1 for WilliamsonShmoys.exists_triangulated_planar_supergraph
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-25T23:34:14.533889+00:00
-- url     : https://prove2.me/submissions/95ce0f6c-a37d-4387-ba95-0077c03bc031

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_for_triangulation_target
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_for_triangulation_target

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V)
    (hconn : ∀ u v : V, Nonempty (G.Walk u v)) :
    ∃ H : SimpleGraph V, G ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      G.edgeSet.ncard ≤ H.edgeSet.ncard ∧
      H.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨H, hGH, hH, hmono, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph_for_triangulation_target G hG
  have hcount :=
    WilliamsonShmoys.maximal_planar_edge_count_for_triangulation_target H hH hV hmax
  exact ⟨H, hGH, hH, hmono, hcount⟩
-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_triangulated_supergraph
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T13:32:33.061965+00:00
-- url     : https://prove2.me/submissions/7070e521-1292-4e13-b61f-9f9b7d19ebfb

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_planar_supergraph_maximal_extension
import Theorems.Thm_WilliamsonShmoys_edge_maximal_planar_graph_has_euler_edge_count

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      H <= K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
        K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨K, hHK, hK, hmax⟩ :=
    WilliamsonShmoys.finite_planar_supergraph_maximal_extension H hH
  exact ⟨K, hHK, hK,
    WilliamsonShmoys.edge_maximal_planar_graph_has_euler_edge_count K hV hK hmax⟩
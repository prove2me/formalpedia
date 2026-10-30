-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_extension_exact_edge_count
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T10:23:00.757881+00:00
-- url     : https://prove2.me/submissions/e1130181-bb0e-4170-be59-fd5df5a9cf83

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_maximal_drawable
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_exact_edge_count

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ J : SimpleGraph V,
      H ≤ J ∧
      WilliamsonShmoys.HasPlanarDrawingOn J ∧
      J.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨J, hHJ, hJ, hmax⟩ :=
    WilliamsonShmoys.planar_supergraph_maximal_drawable H hH
  exact ⟨J, hHJ, hJ,
    WilliamsonShmoys.maximal_planar_graph_exact_edge_count J hV hJ hmax⟩
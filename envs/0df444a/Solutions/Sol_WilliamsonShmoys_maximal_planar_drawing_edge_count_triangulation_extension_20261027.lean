-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count_triangulation_extension_20261027
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T19:40:14.070437+00:00
-- url     : https://prove2.me/submissions/cd6531bd-3023-446d-9e2f-a7dd6dfababe

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_extension_for_edge_count_20261027
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_count_20261027

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ J : SimpleGraph V,
      H.edgeSet ⊆ J.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn J ∧
      J.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨J, hHJ, hJplanar, hJmax⟩ :=
    WilliamsonShmoys.planar_drawing_extension_for_edge_count_20261027 H hV hH
  refine ⟨J, hHJ, hJplanar, ?_⟩
  exact WilliamsonShmoys.maximal_drawable_graph_edge_count_20261027 J hV hJplanar hJmax
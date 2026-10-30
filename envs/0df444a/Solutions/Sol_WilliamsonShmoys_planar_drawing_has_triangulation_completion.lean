-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_has_triangulation_completion
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T15:28:22.038756+00:00
-- url     : https://prove2.me/submissions/9cda6a4a-66b5-4a7e-9648-fe3e20244039

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_maximal_drawable_supergraph_e51c1790
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count_e51c1790

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hT : WilliamsonShmoys.HasPlanarDrawingOn T) :
    ∃ U : SimpleGraph V,
      T ≤ U ∧
      WilliamsonShmoys.HasPlanarDrawingOn U ∧
      3 * Fintype.card V = U.edgeSet.ncard + 6 := by
  obtain ⟨U, hTU, hU, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_has_maximal_drawable_supergraph_e51c1790 T hT
  have hedge :=
    WilliamsonShmoys.maximal_planar_graph_edge_count_e51c1790 U hV hU hmax
  exact ⟨U, hTU, hU, hedge⟩
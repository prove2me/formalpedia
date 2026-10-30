-- Prove2me | solution 1 for WilliamsonShmoys.drawable_triangulation_edge_count
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T16:52:05.499109+00:00
-- url     : https://prove2.me/submissions/e2f12709-1da9-4178-9d99-19920a71f3af

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_drawable_extension_maximal_for_edge_count
import Theorems.Thm_WilliamsonShmoys_triangulation_edge_count_of_maximal_drawable

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ U : SimpleGraph V, G ≤ U ∧
      WilliamsonShmoys.HasPlanarDrawingOn U ∧
      U.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨U, hGU, hU, hmax⟩ :=
    WilliamsonShmoys.drawable_extension_maximal_for_edge_count G hG
  refine ⟨U, hGU, hU, ?_⟩
  exact WilliamsonShmoys.triangulation_edge_count_of_maximal_drawable U hV hU hmax

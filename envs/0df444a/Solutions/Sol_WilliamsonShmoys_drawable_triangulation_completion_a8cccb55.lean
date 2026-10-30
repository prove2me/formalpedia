-- Prove2me | solution 1 for WilliamsonShmoys.drawable_triangulation_completion_a8cccb55
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T13:41:04.329121+00:00
-- url     : https://prove2.me/submissions/73f98cdb-a44c-4d73-ac81-9c07dd5bd0c9

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_drawable_supergraph_a8cccb55
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_edge_count_a8cccb55

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (W : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hW : WilliamsonShmoys.HasPlanarDrawingOn W) :
    ∃ U : SimpleGraph V,
      W ≤ U ∧
      WilliamsonShmoys.HasPlanarDrawingOn U ∧
      U.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨U, hWU, hU, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_drawable_supergraph_a8cccb55 W hV hW
  have hcount :=
    WilliamsonShmoys.maximal_drawable_edge_count_a8cccb55 U hV hU hmax
  exact ⟨U, hWU, hU, hcount⟩
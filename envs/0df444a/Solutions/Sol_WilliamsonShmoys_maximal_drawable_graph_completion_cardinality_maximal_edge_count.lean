-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_graph_completion_cardinality_maximal_edge_count
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T13:19:54.581992+00:00
-- url     : https://prove2.me/submissions/e2c06bee-5e97-439d-9c40-d3e74b75f1c0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bound_a8cccb55
import Theorems.Thm_WilliamsonShmoys_drawable_triangulation_completion_a8cccb55

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (W : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hW : WilliamsonShmoys.HasPlanarDrawingOn W)
    (hmax : ∀ U : SimpleGraph V,
      W ≤ U → WilliamsonShmoys.HasPlanarDrawingOn U → U ≤ W) :
    W.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hupper := WilliamsonShmoys.planar_drawing_edge_bound_a8cccb55 W hV hW
  obtain ⟨U, hWU, hU, hUcount⟩ :=
    WilliamsonShmoys.drawable_triangulation_completion_a8cccb55 W hV hW
  have hUW := hmax U hWU hU
  have hEq : U = W := le_antisymm hUW hWU
  have hlower : 3 * Fintype.card V ≤ W.edgeSet.ncard + 6 := by
    simpa [hEq] using (le_of_eq hUcount.symm)
  omega
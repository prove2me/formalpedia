-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_for_triangulation_completion
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T06:45:39.946795+00:00
-- url     : https://prove2.me/submissions/e3e39034-cb43-42ae-9185-f51ab825725a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_drawable_graph_has_triangulation_completion_edge_count

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn T)
    (hV : 3 <= Fintype.card V)
    (hmax : ∀ U : SimpleGraph V,
      (∀ {u v}, T.Adj u v → U.Adj u v) →
      WilliamsonShmoys.HasPlanarDrawingOn U →
      ∀ {u v}, U.Adj u v → T.Adj u v) :
    T.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨U, hTU, hUdraw, hUncard⟩ :=
    WilliamsonShmoys.drawable_graph_has_triangulation_completion_edge_count T hdraw hV
  have hUT : ∀ {u v}, U.Adj u v → T.Adj u v := hmax U hTU hUdraw
  have hEq : T = U := by
    ext u v
    exact ⟨hTU, hUT⟩
  rw [hEq]
  exact hUncard
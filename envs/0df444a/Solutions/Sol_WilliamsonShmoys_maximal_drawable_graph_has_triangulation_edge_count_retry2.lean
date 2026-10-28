-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_graph_has_triangulation_edge_count_retry2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T18:32:13.669487+00:00
-- url     : https://prove2.me/submissions/29814c13-1482-418b-b4cc-c8485d624a3e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_drawable_graph_has_triangulated_extension

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (W : SimpleGraph V)
    (hWdraw : WilliamsonShmoys.HasPlanarDrawingOn W)
    (hCard : 3 <= Fintype.card V)
    (hmax : forall X : SimpleGraph V, W <= X ->
      WilliamsonShmoys.HasPlanarDrawingOn X -> X <= W) :
    3 * Fintype.card V = W.edgeSet.ncard + 6 := by
  obtain ⟨X, hWX, hXdraw, hXcount⟩ :=
    WilliamsonShmoys.drawable_graph_has_triangulated_extension W hWdraw hCard
  have hXW : X <= W := hmax X hWX hXdraw
  have hEq : X = W := le_antisymm hXW hWX
  simpa [hEq] using hXcount
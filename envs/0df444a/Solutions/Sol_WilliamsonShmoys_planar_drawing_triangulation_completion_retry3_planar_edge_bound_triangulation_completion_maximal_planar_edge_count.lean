-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_triangulation_completion_retry3_planar_edge_bound_triangulation_completion_maximal_planar_edge_count
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T12:41:29.498015+00:00
-- url     : https://prove2.me/submissions/42cd1e57-cf9f-4001-832f-cf33904d4271

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_completion_retry3_planar_edge_bound_triangulation_completion_maximal_planar_edge_count_exists_triangulation_completion

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V) (hDraw : HasPlanarDrawingOn T)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ U : SimpleGraph V, T ≤ U → HasPlanarDrawingOn U → U ≤ T) :
    T.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨U, hTU, hUDraw, hCount⟩ :=
    WilliamsonShmoys.planar_drawing_triangulation_completion_retry3_planar_edge_bound_triangulation_completion_maximal_planar_edge_count_exists_triangulation_completion
      T hDraw hCard
  have hUT : U ≤ T := hMax U hTU hUDraw
  have hEq : T = U := le_antisymm hTU hUT
  simpa only [hEq] using hCount
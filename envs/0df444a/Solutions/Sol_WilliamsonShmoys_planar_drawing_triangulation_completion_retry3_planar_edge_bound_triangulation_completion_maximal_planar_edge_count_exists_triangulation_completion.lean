-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_triangulation_completion_retry3_planar_edge_bound_triangulation_completion_maximal_planar_edge_count_exists_triangulation_completion
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T13:11:40.147572+00:00
-- url     : https://prove2.me/submissions/a65b78d9-7725-4dc6-a9dc-2e584e91b25d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_drawable_supergraph_e61f28a9_retry3
import Theorems.Thm_WilliamsonShmoys_edge_count_of_maximal_planar_drawing_e61f28a9_retry3

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V) (hDraw : HasPlanarDrawingOn T)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ U : SimpleGraph V, T ≤ U ∧ HasPlanarDrawingOn U ∧
      U.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨U, hTU, hDrawU, hMax⟩ :=
    WilliamsonShmoys.exists_maximal_drawable_supergraph_e61f28a9_retry3 T hDraw
  exact ⟨U, hTU, hDrawU,
    WilliamsonShmoys.edge_count_of_maximal_planar_drawing_e61f28a9_retry3 U hDrawU hCard hMax⟩
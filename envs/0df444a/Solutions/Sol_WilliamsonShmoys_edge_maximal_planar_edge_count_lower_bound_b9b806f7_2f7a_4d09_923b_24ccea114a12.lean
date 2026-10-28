-- Prove2me | solution 1 for WilliamsonShmoys.edge_maximal_planar_edge_count_lower_bound_b9b806f7_2f7a_4d09_923b_24ccea114a12
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T10:47:08.85167+00:00
-- url     : https://prove2.me/submissions/eeb77bc7-0897-4c29-8690-6566b5545b6a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_edge_maximal_planar_drawing_exact_edge_count_b9b806f7_2f7a_4d09_923b_24ccea114a12

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hMax : forall K : SimpleGraph V,
      M <= K -> WilliamsonShmoys.HasPlanarDrawingOn K -> K <= M) :
    3 * Fintype.card V <= M.edgeSet.ncard + 6 := by
  have hCount := WilliamsonShmoys.edge_maximal_planar_drawing_exact_edge_count_b9b806f7_2f7a_4d09_923b_24ccea114a12
    M hV hM hMax
  exact le_of_eq hCount
-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count_from_embedding
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T07:57:18.962965+00:00
-- url     : https://prove2.me/submissions/c188972e-10c5-4b81-b791-95094a77694b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_35554814_repair3
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound_35554814_repair3

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V)
    (hCard : 3 <= Fintype.card V)
    (hP : WilliamsonShmoys.HasPlanarDrawingOn P)
    (hMax : forall Q : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn Q ->
      Set.Subset P.edgeSet Q.edgeSet -> Set.Subset Q.edgeSet P.edgeSet) :
    P.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hUpper :=
    WilliamsonShmoys.planar_edge_count_upper_bound_35554814_repair3 P hCard hP
  have hLower :=
    WilliamsonShmoys.maximal_planar_edge_count_lower_bound_35554814_repair3
      P hCard hP hMax
  omega
-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count_repair3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T00:52:58.202642+00:00
-- url     : https://prove2.me/submissions/4ae7fdbf-f6d4-4aea-bde1-b7a99b0a671b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_count_upper_bound_repair3
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_lower_bound_repair3

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hT : HasPlanarDrawingOn T)
    (hCard : 3 ≤ Fintype.card V)
    (hmax : ∀ U : SimpleGraph V,
      HasPlanarDrawingOn U →
      (∀ u v, T.Adj u v → U.Adj u v) →
      (∀ u v, U.Adj u v → T.Adj u v)) :
    T.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hUpper :=
    WilliamsonShmoys.planar_drawing_edge_count_upper_bound_repair3 T hT hCard
  have hLower :=
    WilliamsonShmoys.maximal_planar_drawing_edge_count_lower_bound_repair3
      T hT hCard hmax
  omega
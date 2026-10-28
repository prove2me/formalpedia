-- Prove2me | solution 1 for WilliamsonShmoys.edge_count_of_maximal_planar_drawing_e61f28a9_retry3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T13:45:06.179467+00:00
-- url     : https://prove2.me/submissions/a22784c9-d59c-4ed1-bcef-bc5b415711d9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_edge_count_planar_upper_retry3
import Theorems.Thm_WilliamsonShmoys_edge_count_maximal_planar_lower_retry3

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (U : SimpleGraph V) (hDraw : HasPlanarDrawingOn U)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ W : SimpleGraph V, U ≤ W → HasPlanarDrawingOn W → W = U) :
    U.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  have hUpper :=
    WilliamsonShmoys.edge_count_planar_upper_retry3 U hDraw hCard
  have hLower :=
    WilliamsonShmoys.edge_count_maximal_planar_lower_retry3 U hDraw hCard hMax
  omega
-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_for_edge_count_bound_v2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T17:28:22.485975+00:00
-- url     : https://prove2.me/submissions/f2ddb0d7-7f4e-4d57-8e29-dd30ebb2ee18
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_count_upper_bound_06232b3e
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_lower_bound_06232b3e

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V)
    (hmax : ∀ K : SimpleGraph V, L ≤ K → HasPlanarDrawingOn K → K = L) :
    L.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  have hupper :=
    WilliamsonShmoys.planar_drawing_edge_count_upper_bound_06232b3e L hL hCard
  have hlower :=
    WilliamsonShmoys.maximal_planar_drawing_edge_count_lower_bound_06232b3e
      L hL hCard hmax
  omega
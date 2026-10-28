-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawingOn_edge_count_279755a6_02cd_4483_9b65_417cbe6cd492
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T17:44:58.714504+00:00
-- url     : https://prove2.me/submissions/1d3184a7-ea13-4f1f-a50d-9ad664397f8e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_upper_bound_707fd91e
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_lower_bound_707fd91e

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : forall L : SimpleGraph V,
      K <= L -> WilliamsonShmoys.HasPlanarDrawingOn L -> L = K) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  exact Nat.le_antisymm
    (WilliamsonShmoys.planar_drawing_edge_upper_bound_707fd91e K hV hK)
    (WilliamsonShmoys.maximal_planar_drawing_edge_lower_bound_707fd91e K hV hK hmax)
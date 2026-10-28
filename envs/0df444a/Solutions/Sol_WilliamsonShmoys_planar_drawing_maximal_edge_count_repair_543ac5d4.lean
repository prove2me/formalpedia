-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_maximal_edge_count_repair_543ac5d4
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T06:21:53.840907+00:00
-- url     : https://prove2.me/submissions/ad1a0648-9379-49a3-92df-1b459442454a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_edge_count_repair_543ac5d4_edge_upper
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_edge_count_repair_543ac5d4_edge_lower

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (U : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hU : WilliamsonShmoys.HasPlanarDrawingOn U)
    (hmax : ∀ W : SimpleGraph V,
      U <= W →
      WilliamsonShmoys.HasPlanarDrawingOn W →
      W = U) :
    3 * Fintype.card V = U.edgeSet.ncard + 6 := by
  have hu := WilliamsonShmoys.planar_drawing_maximal_edge_count_repair_543ac5d4_edge_upper U hV hU
  have hl := WilliamsonShmoys.planar_drawing_maximal_edge_count_repair_543ac5d4_edge_lower U hV hU hmax
  omega
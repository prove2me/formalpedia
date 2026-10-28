-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count_for_edge_count_completion
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T02:29:35.728762+00:00
-- url     : https://prove2.me/submissions/0759fa4f-f682-4995-a0f9-aaccf60e797f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_upper_bound_20261028
import Theorems.Thm_WilliamsonShmoys_planar_maximal_edge_lower_bound_20261028

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ L : SimpleGraph V, K ≤ L →
      WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ K) :
    3 * Fintype.card V = K.edgeSet.ncard + 6 := by
  have hupper :=
    WilliamsonShmoys.planar_drawing_edge_upper_bound_20261028 K hK hCard
  have hlower :=
    WilliamsonShmoys.planar_maximal_edge_lower_bound_20261028 K hK hCard hMax
  omega
-- Prove2me | solution 1 for WilliamsonShmoys.edge_count_of_maximal_planar_drawing_fab67c4d
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T05:10:42.415987+00:00
-- url     : https://prove2.me/submissions/ed68c8f2-3481-49e9-b259-a9f2490da71c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_fab67c4d
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound_fab67c4d

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ M : SimpleGraph V, L.edgeSet ⊂ M.edgeSet →
      ¬ WilliamsonShmoys.HasPlanarDrawingOn M) :
    (L.edgeSet.ncard : Int) = 3 * (Fintype.card V : Int) - 6 := by
  have hupper :=
    WilliamsonShmoys.planar_edge_count_upper_bound_fab67c4d L hL hCard
  have hlower :=
    WilliamsonShmoys.maximal_planar_edge_count_lower_bound_fab67c4d L hL hCard hMax
  omega
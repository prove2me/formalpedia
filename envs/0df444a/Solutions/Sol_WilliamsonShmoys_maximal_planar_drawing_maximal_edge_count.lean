-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_maximal_edge_count
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T11:12:38.871985+00:00
-- url     : https://prove2.me/submissions/06d55623-e4ea-4b09-be3d-9ed09f30f0e8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_count_upper_bound_repair_20261027
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_lower_bound_repair_20261027

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hdraw : HasPlanarDrawingOn L)
    (hmax : ∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M ≤ L) :
    L.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  have hupper : L.edgeSet.ncard ≤ 3 * Fintype.card V - 6 :=
    WilliamsonShmoys.planar_drawing_edge_count_upper_bound_repair_20261027 L hV hdraw
  have hlower : 3 * Fintype.card V - 6 ≤ L.edgeSet.ncard :=
    WilliamsonShmoys.maximal_planar_drawing_edge_count_lower_bound_repair_20261027
      L hV hdraw hmax
  exact Nat.le_antisymm hupper hlower
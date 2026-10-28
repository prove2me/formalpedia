-- Prove2me | solution 1 for WilliamsonShmoys.edge_maximal_planar_edge_count_20261026
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T03:35:04.033124+00:00
-- url     : https://prove2.me/submissions/4741eddd-7d35-436c-9e01-0dd185198d8f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_edge_maximal_planar_edge_count_upper
import Theorems.Thm_WilliamsonShmoys_edge_maximal_planar_edge_count_lower

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ J : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn J →
      (∀ ⦃u v : V⦄, H.Adj u v → J.Adj u v) → J = H)
    (hV : 3 ≤ Fintype.card V) :
    H.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  apply le_antisymm
  · exact WilliamsonShmoys.edge_maximal_planar_edge_count_upper H hH hV
  · exact WilliamsonShmoys.edge_maximal_planar_edge_count_lower H hH hmax hV
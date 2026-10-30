-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_has_triangulation_edge_count
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T09:12:17.756685+00:00
-- url     : https://prove2.me/submissions/6501a93e-7e5f-49c9-b2dc-148615581331

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_edge_count_202d559d

set_option autoImplicit false

open WilliamsonShmoys
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hmax : ∀ M : SimpleGraph V, L ≤ M →
      WilliamsonShmoys.HasPlanarDrawingOn M → M = L) :
    L.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  first
  | exact _root_.WilliamsonShmoys.maximal_drawable_edge_count_202d559d
  | (apply _root_.WilliamsonShmoys.maximal_drawable_edge_count_202d559d <;> assumption)
  | (intros; apply _root_.WilliamsonShmoys.maximal_drawable_edge_count_202d559d <;> assumption)

-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_has_maximal_edge_count
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T13:45:30.280992+00:00
-- url     : https://prove2.me/submissions/ea65e6d9-30b5-4124-b97a-24c9e471e532

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_has_triangulation_edge_count

set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hmax : ∀ M : SimpleGraph V, L ≤ M →
      WilliamsonShmoys.HasPlanarDrawingOn M → M = L) :
    L.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  first
  | exact _root_.WilliamsonShmoys.maximal_planar_has_triangulation_edge_count
  | (apply _root_.WilliamsonShmoys.maximal_planar_has_triangulation_edge_count <;> assumption)
  | (intros; apply _root_.WilliamsonShmoys.maximal_planar_has_triangulation_edge_count <;> assumption)

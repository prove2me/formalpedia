-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_extension_edge_upper_bound_51bf81b4_48bc_4660_b9e1_3005ea79cb82
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T13:42:57.174714+00:00
-- url     : https://prove2.me/submissions/16a92cf2-51bf-44e2-bf11-85ae1193e74c

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_bound

set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    M.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  first
  | exact _root_.WilliamsonShmoys.planar_edge_bound
  | (apply _root_.WilliamsonShmoys.planar_edge_bound <;> assumption)
  | (intros; apply _root_.WilliamsonShmoys.planar_edge_bound <;> assumption)

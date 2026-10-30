-- Prove2me | solution 2 for WilliamsonShmoys.planar_edge_upper_bound_repair_20261026
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T10:02:55.121224+00:00
-- url     : https://prove2.me/submissions/48a5ffc9-1bc6-44fa-9632-5b7b29370fb0

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_ef555edc

open WilliamsonShmoys

set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    K.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  first
  | exact _root_.WilliamsonShmoys.planar_edge_count_upper_bound_ef555edc
  | (apply _root_.WilliamsonShmoys.planar_edge_count_upper_bound_ef555edc <;> assumption)
  | (intros; apply _root_.WilliamsonShmoys.planar_edge_count_upper_bound_ef555edc <;> assumption)

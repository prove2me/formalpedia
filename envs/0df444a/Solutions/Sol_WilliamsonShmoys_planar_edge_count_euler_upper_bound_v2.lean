-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_euler_upper_bound_v2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T09:53:27.16858+00:00
-- url     : https://prove2.me/submissions/9348cdef-9626-42cc-af23-10b87ab78099

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Basic
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_ef555edc

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

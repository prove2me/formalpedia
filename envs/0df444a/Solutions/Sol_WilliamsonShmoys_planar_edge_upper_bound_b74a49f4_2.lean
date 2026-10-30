-- Prove2me | solution 2 for WilliamsonShmoys.planar_edge_upper_bound_b74a49f4
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T09:11:40.871956+00:00
-- url     : https://prove2.me/submissions/fb4ac88c-f27c-45e9-9712-d7dbd97219f2

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_upper_bound_20261028

set_option autoImplicit false
theorem solution {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hK : WilliamsonShmoys.HasPlanarDrawingOn K) (hCard : 3 ≤ Fintype.card V) : K.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  first
  | exact _root_.WilliamsonShmoys.planar_drawing_edge_upper_bound_20261028
  | (apply _root_.WilliamsonShmoys.planar_drawing_edge_upper_bound_20261028 <;> assumption)
  | (intros; apply _root_.WilliamsonShmoys.planar_drawing_edge_upper_bound_20261028 <;> assumption)

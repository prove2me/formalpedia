-- Prove2me | solution 2 for WilliamsonShmoys.planar_edge_count_le__p2m_bd86803d_f791_454d_9e3d_cf8ce9ce0da0_a1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T13:34:18.776988+00:00
-- url     : https://prove2.me/submissions/61abc3a1-1a42-4107-ae45-f3d26fb0bc37

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_on

set_option autoImplicit false

open WilliamsonShmoys
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  first
  | exact _root_.WilliamsonShmoys.planar_edge_count_upper_bound_on
  | (apply _root_.WilliamsonShmoys.planar_edge_count_upper_bound_on <;> assumption)
  | (intros; apply _root_.WilliamsonShmoys.planar_edge_count_upper_bound_on <;> assumption)

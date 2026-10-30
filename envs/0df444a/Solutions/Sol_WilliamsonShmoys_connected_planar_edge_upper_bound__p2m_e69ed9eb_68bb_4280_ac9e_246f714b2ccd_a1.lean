-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_edge_upper_bound__p2m_e69ed9eb_68bb_4280_ac9e_246f714b2ccd_a1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T13:37:03.096258+00:00
-- url     : https://prove2.me/submissions/f05015e6-6096-461d-9a81-0d7440968167

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_edge_bound_core
open WilliamsonShmoys
theorem solution {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G) (hConn : G.Connected) (hCard : 3 ≤ Fintype.card V) : G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  first
  | exact _root_.WilliamsonShmoys.connected_planar_drawing_edge_bound_core
  | (apply _root_.WilliamsonShmoys.connected_planar_drawing_edge_bound_core <;> assumption)
  | (intros; apply _root_.WilliamsonShmoys.connected_planar_drawing_edge_bound_core <;> assumption)

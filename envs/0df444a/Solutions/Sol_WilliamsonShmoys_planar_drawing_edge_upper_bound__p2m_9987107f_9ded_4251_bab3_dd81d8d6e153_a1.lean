-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_upper_bound__p2m_9987107f_9ded_4251_bab3_dd81d8d6e153_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:27:36.003574+00:00
-- url     : https://prove2.me/submissions/8ceeb3fa-f5ca-42a1-9b9a-dd26cb65666b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_upper_bound_connected_case__p2m_263e0430_0bed_4695_a55f_33a5be744a5b_a1
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_upper_bound_component_reduction__p2m_263e0430_0bed_4695_a55f_33a5be744a5b_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hN : HasPlanarDrawingOn N) :
    (letI : DecidableRel N.Adj := Classical.decRel N.Adj;
     N.edgeFinset.card + 6 <= 3 * Fintype.card V) := by
  exact WilliamsonShmoys.planar_drawing_edge_upper_bound_component_reduction__p2m_263e0430_0bed_4695_a55f_33a5be744a5b_a1
    N hV hN (fun G hW hconn hG =>
      WilliamsonShmoys.planar_drawing_edge_upper_bound_connected_case__p2m_263e0430_0bed_4695_a55f_33a5be744a5b_a1
        G hW hconn hG)
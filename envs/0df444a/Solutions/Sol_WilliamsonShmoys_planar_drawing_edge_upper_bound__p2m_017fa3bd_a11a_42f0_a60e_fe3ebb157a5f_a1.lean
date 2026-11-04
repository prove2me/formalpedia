-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_upper_bound__p2m_017fa3bd_a11a_42f0_a60e_fe3ebb157a5f_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-03T16:40:11.163222+00:00
-- url     : https://prove2.me/submissions/90edbfba-67a3-4a84-a9c6-682425310478

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_upper_bound_component_reduction__p2m_263e0430_0bed_4695_a55f_33a5be744a5b_a1
import Theorems.Thm_WilliamsonShmoys_connected_planar_euler_bound__p2m_fa5d736f_5e40_4868_bcf6_007f98212d2a_a1
import Mathlib

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hM : HasPlanarDrawingOn M)
    (hV : 3 ≤ Fintype.card V) :
    (letI : DecidableRel M.Adj := Classical.decRel M.Adj;
     M.edgeFinset.card + 6 ≤ 3 * Fintype.card V) := by
  apply WilliamsonShmoys.planar_drawing_edge_upper_bound_component_reduction__p2m_263e0430_0bed_4695_a55f_33a5be744a5b_a1 M hV hM
  intro W _ _ G hW hconn hG
  exact WilliamsonShmoys.connected_planar_euler_bound__p2m_fa5d736f_5e40_4868_bcf6_007f98212d2a_a1 G hG hconn hW

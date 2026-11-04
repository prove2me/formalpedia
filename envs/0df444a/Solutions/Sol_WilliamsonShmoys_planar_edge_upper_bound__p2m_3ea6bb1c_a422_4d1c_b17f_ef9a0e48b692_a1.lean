-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_upper_bound__p2m_3ea6bb1c_a422_4d1c_b17f_ef9a0e48b692_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-03T16:36:44.396384+00:00
-- url     : https://prove2.me/submissions/049104a8-77b2-4b8c-8dcc-414361e65052

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_upper_bound_component_reduction__p2m_263e0430_0bed_4695_a55f_33a5be744a5b_a1
import Theorems.Thm_WilliamsonShmoys_connected_planar_euler_bound__p2m_fa5d736f_5e40_4868_bcf6_007f98212d2a_a1
import Mathlib

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V) :
    letI : DecidableRel K.Adj := Classical.decRel K.Adj
    letI : Fintype ↑K.edgeSet := Fintype.ofFinite _
    K.edgeFinset.card + 6 ≤ 3 * Fintype.card V := by
  have h := WilliamsonShmoys.planar_drawing_edge_upper_bound_component_reduction__p2m_263e0430_0bed_4695_a55f_33a5be744a5b_a1 K hV hK (by
    intro W instF instL G hW hconn hG
    exact WilliamsonShmoys.connected_planar_euler_bound__p2m_fa5d736f_5e40_4868_bcf6_007f98212d2a_a1 G hG hconn hW)
  convert h using 1 <;> congr 2 <;> ext e <;> simp
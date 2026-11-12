-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_upper_bound__p2m_b1eeea0d_0264_4037_a9be_26c96369c701_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T03:10:14.86644+00:00
-- url     : https://prove2.me/submissions/c527e0a9-c60a-473c-ba09-48b6b64140be

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_componentwise_edge_bound_aggregate__p2m_c4d63dfe_c88f_43bb_a642_10d75b5a8453_a2
import Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_edge_bound__p2m_c4d63dfe_c88f_43bb_a642_10d75b5a8453_a2
import Theorems.Thm_WilliamsonShmoys_planar_drawing_induce__p2m_c4d63dfe_c88f_43bb_a642_10d75b5a8453_a2

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    K.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  apply WilliamsonShmoys.componentwise_edge_bound_aggregate__p2m_c4d63dfe_c88f_43bb_a642_10d75b5a8453_a2
      (K := K) hcard
  intro S hS hconn
  have hdraw :
      WilliamsonShmoys.HasPlanarDrawingOn
        (K.induce (↑S : Set V)) :=
    WilliamsonShmoys.planar_drawing_induce__p2m_c4d63dfe_c88f_43bb_a642_10d75b5a8453_a2
      K S hK
  simpa using
    (WilliamsonShmoys.connected_planar_drawing_edge_bound__p2m_c4d63dfe_c88f_43bb_a642_10d75b5a8453_a2
      (K.induce (↑S : Set V)) (by simpa using hS) hconn hdraw)
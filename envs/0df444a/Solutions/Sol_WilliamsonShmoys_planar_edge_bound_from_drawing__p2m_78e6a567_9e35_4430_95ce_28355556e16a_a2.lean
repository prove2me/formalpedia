-- Prove2me | solution 1 for WilliamsonShmoys_planar_edge_bound_from_drawing__p2m_78e6a567_9e35_4430_95ce_28355556e16a_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:51:58.056667+00:00
-- url     : https://prove2.me/submissions/3ace0bea-faf6-4dd6-92ce-f95ad51e49de

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_maximal_planar_extension_on_same_vertices__p2m_45533a44_b035_4e47_8a66_77352d0d9780_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_has_three_n_minus_six_edges__p2m_45533a44_b035_4e47_8a66_77352d0d9780_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hconn : K.Connected)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    K.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  obtain ⟨L, hKL, hmono, hplanar, hMax⟩ :=
    WilliamsonShmoys_maximal_planar_extension_on_same_vertices__p2m_45533a44_b035_4e47_8a66_77352d0d9780_a1
      K hcard hconn hK
  have htri :=
    WilliamsonShmoys_maximal_planar_graph_has_three_n_minus_six_edges__p2m_45533a44_b035_4e47_8a66_77352d0d9780_a1
      L hcard hplanar hMax
  calc
    K.edgeSet.ncard ≤ L.edgeSet.ncard := hmono
    _ = 3 * Fintype.card V - 6 := htri
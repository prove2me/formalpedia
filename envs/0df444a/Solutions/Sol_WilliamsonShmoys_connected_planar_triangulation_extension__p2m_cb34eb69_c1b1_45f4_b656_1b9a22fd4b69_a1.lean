-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_triangulation_extension__p2m_cb34eb69_c1b1_45f4_b656_1b9a22fd4b69_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T01:05:12.918845+00:00
-- url     : https://prove2.me/submissions/3286f182-8afb-4cd4-bb8d-f74952bd1a26

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_edge_maximal_planar_extension__p2m_e657dedf_589f_4338_b1cf_3cbd004df18d_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_e657dedf_589f_4338_b1cf_3cbd004df18d_a1
import Mathlib
open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V) (hconn : H.Connected)
    (hH : HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V, H ≤ K ∧ HasPlanarDrawingOn K ∧
      H.edgeSet.ncard ≤ K.edgeSet.ncard ∧
      K.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨K, hHK, hKplanar, hKconn, hKmax, hmono⟩ :=
    WilliamsonShmoys_edge_maximal_planar_extension__p2m_e657dedf_589f_4338_b1cf_3cbd004df18d_a1
      H hV hconn hH
  have hcount := WilliamsonShmoys_maximal_planar_edge_count__p2m_e657dedf_589f_4338_b1cf_3cbd004df18d_a1
    K hV hKconn hKplanar hKmax
  exact ⟨K, hHK, hKplanar, hmono, hcount⟩
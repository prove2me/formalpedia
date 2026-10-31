-- Prove2me | solution 1 for WilliamsonShmoys.planar_graph_has_triangulating_supergraph__p2m_af48b21b_c55d_4bf2_b112_9c52085bd66b_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:47:03.010237+00:00
-- url     : https://prove2.me/submissions/9ac7c737-bf79-4abf-a936-cef75092fec1

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph__p2m_5e849ad0_992f_4795_a8f1_d28ee483fe3d_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_5e849ad0_992f_4795_a8f1_d28ee483fe3d_a1

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
        L.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨L, hKL, hDrawL, hMax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_5e849ad0_992f_4795_a8f1_d28ee483fe3d_a1
      K hDraw
  refine ⟨L, hKL, hDrawL, ?_⟩
  exact WilliamsonShmoys.maximal_planar_edge_count__p2m_5e849ad0_992f_4795_a8f1_d28ee483fe3d_a1
    L hDrawL hV hMax
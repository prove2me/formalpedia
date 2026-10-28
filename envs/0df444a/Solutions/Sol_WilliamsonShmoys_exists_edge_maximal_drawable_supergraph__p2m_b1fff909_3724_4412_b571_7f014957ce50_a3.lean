-- Prove2me | solution 1 for WilliamsonShmoys.exists_edge_maximal_drawable_supergraph__p2m_b1fff909_3724_4412_b571_7f014957ce50_a3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T19:38:58.932235+00:00
-- url     : https://prove2.me/submissions/ef613177-d2d2-44b2-98bc-8a34f6908485

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_max_edge_count_supergraph__p2m_eef664be_1603_4195_b44b_d81e1ccffc6c_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn J) :
    ∃ K : SimpleGraph V, J ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L →
        L.edgeSet.ncard ≤ K.edgeSet.ncard := by
  exact WilliamsonShmoys.exists_max_edge_count_supergraph__p2m_eef664be_1603_4195_b44b_d81e1ccffc6c_a1
    J WilliamsonShmoys.HasPlanarDrawingOn hDraw
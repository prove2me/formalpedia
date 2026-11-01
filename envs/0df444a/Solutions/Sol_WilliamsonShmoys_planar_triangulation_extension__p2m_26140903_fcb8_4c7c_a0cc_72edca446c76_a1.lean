-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_extension__p2m_26140903_fcb8_4c7c_a0cc_72edca446c76_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:50:41.998889+00:00
-- url     : https://prove2.me/submissions/828342db-5a22-4489-853f-89d7cd6ca574

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_extension_maximal__p2m_b4563d71_4874_4d4e_af11_bf65d7ec08a5_a3
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count__p2m_b4563d71_4874_4d4e_af11_bf65d7ec08a5_a3

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hplanar : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
        L.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨L, hKL, hLplanar, hLmax⟩ :=
    WilliamsonShmoys.planar_extension_maximal__p2m_b4563d71_4874_4d4e_af11_bf65d7ec08a5_a3
      K hplanar
  have hcount :=
    WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_b4563d71_4874_4d4e_af11_bf65d7ec08a5_a3
      L hLplanar hcard hLmax
  exact ⟨L, hKL, hLplanar, hcount⟩
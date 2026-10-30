-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_has_maximal_supergraph__p2m_f14f4602_64b2_453c_98d9_533a82cb7d04_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:33:58.978768+00:00
-- url     : https://prove2.me/submissions/67762ed5-ad48-4a57-8dca-52f48e6d9e75

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_graph_property_has_maximal_supergraph__p2m_b95266d4_e515_4cba_bd9d_c9d06115dc07_a2
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ H : SimpleGraph V, K ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
      ∀ J : SimpleGraph V, H ≤ J → WilliamsonShmoys.HasPlanarDrawingOn J → J = H := by
  obtain ⟨H, hKH, hH, hmax⟩ :=
    WilliamsonShmoys.finite_graph_property_has_maximal_supergraph__p2m_b95266d4_e515_4cba_bd9d_c9d06115dc07_a2
      (P := WilliamsonShmoys.HasPlanarDrawingOn) K hK
  exact ⟨H, hKH, hH, hmax⟩
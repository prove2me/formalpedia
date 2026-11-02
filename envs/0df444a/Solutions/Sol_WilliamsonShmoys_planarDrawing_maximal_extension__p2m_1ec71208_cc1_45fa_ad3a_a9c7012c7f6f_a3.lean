-- Prove2me | solution 1 for WilliamsonShmoys.planarDrawing_maximal_extension__p2m_1ec71208_cc1_45fa_ad3a_a9c7012c7f6f_a3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T08:14:04.352492+00:00
-- url     : https://prove2.me/submissions/6cfaf70c-2066-4cd0-98cc-f328133e8323

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planarDrawingOn_subgraph__p2m_f28d325a_badb_43f7_b5e1_caa5a9a8c825_a2
import Theorems.Thm_WilliamsonShmoys_finite_hereditary_maximal__p2m_f28d325a_badb_43f7_b5e1_caa5a9a8c825_a2
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hconn : G.Connected) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
        ∀ K : SimpleGraph V, H ≤ K →
          WilliamsonShmoys.HasPlanarDrawingOn K → K = H := by
  classical
  exact WilliamsonShmoys.finite_hereditary_maximal__p2m_f28d325a_badb_43f7_b5e1_caa5a9a8c825_a2
    (P := WilliamsonShmoys.HasPlanarDrawingOn) G hdraw
    (fun A B hAB hB =>
      WilliamsonShmoys.planarDrawingOn_subgraph__p2m_f28d325a_badb_43f7_b5e1_caa5a9a8c825_a2
        hAB hB)
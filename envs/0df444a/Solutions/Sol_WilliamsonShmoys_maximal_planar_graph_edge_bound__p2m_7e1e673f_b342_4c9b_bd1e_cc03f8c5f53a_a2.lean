-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_edge_bound__p2m_7e1e673f_b342_4c9b_bd1e_cc03f8c5f53a_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T18:49:30.02703+00:00
-- url     : https://prove2.me/submissions/295891f4-ced1-4a78-9b0f-75cbca4feb26

import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_augmentation__p2m_8b750c99_2508_4fa0_8f72_2f809c05bba0_a1
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (R : SimpleGraph V)
    (hCard : 3 <= Fintype.card V)
    (hR : WilliamsonShmoys.HasPlanarDrawingOn R)
    (hMax : ∀ S : SimpleGraph V,
      (∀ u v, R.Adj u v → S.Adj u v) →
      WilliamsonShmoys.HasPlanarDrawingOn S →
      (∀ u v, R.Adj u v → S.Adj u v) → S = R) :
    3 * Fintype.card V - 6 <= R.edgeSet.ncard := by
  obtain ⟨S, hRS, hS, hBound⟩ :=
    WilliamsonShmoys.maximal_planar_graph_augmentation__p2m_8b750c99_2508_4fa0_8f72_2f809c05bba0_a1
      R hCard hR
  have hEq : S = R := hMax S hRS hS hRS
  simpa [hEq] using hBound
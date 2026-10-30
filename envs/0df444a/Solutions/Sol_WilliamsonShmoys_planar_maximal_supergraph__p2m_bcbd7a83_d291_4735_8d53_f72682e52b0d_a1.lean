-- Prove2me | solution 1 for WilliamsonShmoys.planar_maximal_supergraph__p2m_bcbd7a83_d291_4735_8d53_f72682e52b0d_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:44:37.380587+00:00
-- url     : https://prove2.me/submissions/b4d1097e-c758-40ee-84d2-fe399c46cf1c

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_maximal_extension__p2m_6a3d0978_a2a8_418a_a56b_10e4c543dafd_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : HasPlanarDrawingOn M)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ (N : SimpleGraph V) (dN : DecidableRel N.Adj),
      M ≤ N ∧ HasPlanarDrawingOn N ∧
      ∀ K : SimpleGraph V, N ≤ K → HasPlanarDrawingOn K → K = N := by
  classical
  obtain ⟨N, hMN, hN, hmax⟩ :=
    WilliamsonShmoys.finite_maximal_extension__p2m_6a3d0978_a2a8_418a_a56b_10e4c543dafd_a1
      HasPlanarDrawingOn M hM
  exact ⟨N, inferInstance, hMN, hN, hmax⟩

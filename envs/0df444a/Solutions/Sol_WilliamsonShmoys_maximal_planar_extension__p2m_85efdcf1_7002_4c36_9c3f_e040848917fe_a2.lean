-- Prove2me | solution 1 for WilliamsonShmoys_maximal_planar_extension__p2m_85efdcf1_7002_4c36_9c3f_e040848917fe_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T21:52:49.799755+00:00
-- url     : https://prove2.me/submissions/45485e8f-4adf-427d-963a-4f440eed92a5

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_exists_maximal_supergraph_of_finite__p2m_561cdf23_b328_4e27_9dce_aabc2761bd72_a1
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hconn : G.Connected) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      (∀ K : SimpleGraph V, H ≤ K →
        WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ H) ∧
      H.Connected := by
  obtain ⟨H, hGH, hH, hmax⟩ :=
    exists_maximal_supergraph_of_finite__p2m_561cdf23_b328_4e27_9dce_aabc2761bd72_a1
      G WilliamsonShmoys.HasPlanarDrawingOn hG
  exact ⟨H, hGH, hH, hmax, hconn.mono hGH⟩
-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_e23427be_8e8a_4c77_a28e_0966a53f4506_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T03:16:09.587207+00:00
-- url     : https://prove2.me/submissions/d79c8ad5-66f3-40d8-8179-28b927f3ba8a

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_property_maximal_extension__p2m_b6765847_4b48_4473_801c_ad92c775fb51_a2

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N) :
    ∃ H : SimpleGraph V,
      N ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      N.edgeSet.ncard ≤ H.edgeSet.ncard ∧
      (∀ K : SimpleGraph V,
        H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ H) := by
  classical
  obtain ⟨H, hNH, hPlanar, hCount, hMax⟩ :=
    WilliamsonShmoys.finite_property_maximal_extension__p2m_b6765847_4b48_4473_801c_ad92c775fb51_a2
      (V := V) (P := WilliamsonShmoys.HasPlanarDrawingOn) N hN
  exact ⟨H, hNH, hPlanar, hCount, hMax⟩
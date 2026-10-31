-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_5b1667b7_42bc_4fca_8b00_4cc76e33db8b_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T09:46:04.099537+00:00
-- url     : https://prove2.me/submissions/68de8411-86e6-489e-8238-e18723432960

import Theorems.Thm_WilliamsonShmoys_planar_supergraph_edge_lower_bound__p2m_bc33823c_9eaa_4787_b342_ad6547a0cb58_a1
set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (N : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hMax : ∀ P : SimpleGraph V, N ≤ P → WilliamsonShmoys.HasPlanarDrawingOn P → P = N) :
    3 * Fintype.card V - 6 ≤ N.edgeSet.ncard := by
  obtain ⟨P, hNP, hPPlanar, hPBound⟩ :=
    WilliamsonShmoys.planar_supergraph_edge_lower_bound__p2m_bc33823c_9eaa_4787_b342_ad6547a0cb58_a1
      N hCard hN
  have hPN : P = N := hMax P hNP hPPlanar
  simpa [hPN] using hPBound
-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_5e34af62_bc93_4e27_8f77_f0a9265acaf1_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:43:43.174241+00:00
-- url     : https://prove2.me/submissions/ada61fa9-616f-419d-aae9-74f1f4401650

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_supergraph_for_property__p2m_62c66bf3_533d_43c1_bde3_37ac00c5d3e8_a2

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ K : SimpleGraph V, L ≤ K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      (∀ H : SimpleGraph V, K ≤ H → WilliamsonShmoys.HasPlanarDrawingOn H → H ≤ K) := by
  exact WilliamsonShmoys.exists_maximal_supergraph_for_property__p2m_62c66bf3_533d_43c1_bde3_37ac00c5d3e8_a2
    L WilliamsonShmoys.HasPlanarDrawingOn hL
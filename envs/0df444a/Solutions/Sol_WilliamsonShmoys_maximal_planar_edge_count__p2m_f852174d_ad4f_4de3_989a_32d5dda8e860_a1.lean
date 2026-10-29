-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_f852174d_ad4f_4de3_989a_32d5dda8e860_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T20:48:12.118058+00:00
-- url     : https://prove2.me/submissions/204cb51c-f795-4fa6-bf82-7a67ab5b3bda

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_triangulated_supergraph_edge_count__p2m_7671872f_ccc7_461e_8940_29831779f43a_a2

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hMax : ∀ J : SimpleGraph V, H ≤ J →
      WilliamsonShmoys.HasPlanarDrawingOn J → J = H) :
    H.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨J, hHJ, hJ, hCount⟩ :=
    WilliamsonShmoys.exists_triangulated_supergraph_edge_count__p2m_7671872f_ccc7_461e_8940_29831779f43a_a2
      H hCard hH
  have hEq : J = H := hMax J hHJ hJ
  simpa [hEq] using hCount
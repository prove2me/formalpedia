-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_bound__p2m_82506e18_7d6a_422e_80a5_205ab3f947ca_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:58:40.781956+00:00
-- url     : https://prove2.me/submissions/baef775b-c68b-452e-973a-5f8059f9dc97

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_completion__p2m_a74b4731_eea6_44e0_b9ad_6ea707b8b09a_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hDraw : HasPlanarDrawingOn M)
    (hCard : 3 ≤ Fintype.card V) :
    M.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨H, hsub, hcard⟩ :=
    WilliamsonShmoys.planar_drawing_completion__p2m_a74b4731_eea6_44e0_b9ad_6ea707b8b09a_a1
      M hDraw hCard
  have hmono : M.edgeSet.ncard ≤ H.edgeSet.ncard := Set.ncard_mono hsub
  omega
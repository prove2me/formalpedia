-- Prove2me | solution 1 for WilliamsonShmoys.simple_planar_edge_bound__p2m_02b5c4aa_87bb_4609_924c_f8cb942a1930_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:26:07.733171+00:00
-- url     : https://prove2.me/submissions/fe1d4c20-b73b-4f05-b364-98366273b820

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_simple_planar_face_count_bounds__p2m_bff95f57_b2f4_4a78_b638_ad03e6867777_a2

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hconn : G.Connected)
    (hCard : 3 ≤ Fintype.card V) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨f, hEuler, hBoundary⟩ :=
    WilliamsonShmoys.simple_planar_face_count_bounds__p2m_bff95f57_b2f4_4a78_b638_ad03e6867777_a2
      G hG hconn hCard
  omega
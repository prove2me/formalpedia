-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_lower__p2m_8e3b1f8a_4617_463b_ae07_33ab92d25c24_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:55:42.88465+00:00
-- url     : https://prove2.me/submissions/2193d00a-d8f4-47e7-947a-75f44d9139ce

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_supergraph_exact_edge_count

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hDraw : HasPlanarDrawingOn G)
    (hMax : ∀ H : SimpleGraph V, G ≤ H → HasPlanarDrawingOn H → H = G)
    (hCard : 3 ≤ Fintype.card V) :
    3 * Fintype.card V ≤ G.edgeSet.ncard + 6 := by
  obtain ⟨H, hGH, hHDraw, hCount⟩ :=
    WilliamsonShmoys.planar_triangulation_supergraph_exact_edge_count
      G hCard hDraw
  have hEq : H = G := hMax H hGH hHDraw
  rw [hEq] at hCount
  omega
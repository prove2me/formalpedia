-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_completion_edge_count__p2m_c7da917f_6656_4021_9748_8f0ed1f8ec40_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:29:51.733642+00:00
-- url     : https://prove2.me/submissions/d696e934-6530-43cf-8329-e302935ce756

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph__p2m_7ccdbe8d_8a58_4fea_8872_faa4254f94f9_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_7ccdbe8d_8a58_4fea_8872_faa4254f94f9_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      K ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨H, hKH, hHDraw, hMax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_7ccdbe8d_8a58_4fea_8872_faa4254f94f9_a1
      K hDraw
  refine ⟨H, hKH, hHDraw, ?_⟩
  exact WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_7ccdbe8d_8a58_4fea_8872_faa4254f94f9_a1
    H hHDraw hCard (by
      intro J hHJ hJDraw
      exact hMax J (le_trans hKH hHJ) hJDraw)

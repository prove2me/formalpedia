-- Prove2me | solution 1 for WilliamsonShmoys.exists_triangulated_planar_supergraph__p2m_4536f73e_ef32_44ed_9a4a_358d0b7012c5_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:47:25.141733+00:00
-- url     : https://prove2.me/submissions/32d8b214-ec1b-4f12-9efd-177f98f62a5e

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_drawable_maximal_supergraph__p2m_5045813e_840e_441f_8744_eff11fe55168_a2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_5045813e_840e_441f_8744_eff11fe55168_a2

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (J : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn J)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V, J ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨K, hJK, hKDraw, hMax⟩ :=
    WilliamsonShmoys.exists_drawable_maximal_supergraph__p2m_5045813e_840e_441f_8744_eff11fe55168_a2
      J hDraw
  exact ⟨K, hJK, hKDraw,
    WilliamsonShmoys.maximal_planar_edge_count__p2m_5045813e_840e_441f_8744_eff11fe55168_a2
      K hKDraw hMax hCard⟩
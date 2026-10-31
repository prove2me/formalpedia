-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_extension__p2m_b4d3c156_327f_4a72_8089_248d3313a19e_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T06:31:13.954232+00:00
-- url     : https://prove2.me/submissions/72fb6870-a2f0-4184-a81a-7be7948ea41d

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension__p2m_62016e60_61d6_45b8_a392_007d59f3ecc6_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_62016e60_61d6_45b8_a392_007d59f3ecc6_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
        K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨K, hHK, hK, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_extension__p2m_62016e60_61d6_45b8_a392_007d59f3ecc6_a1
      H hH
  have hcount :=
    WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_62016e60_61d6_45b8_a392_007d59f3ecc6_a1
      K hK hmax hV
  exact ⟨K, hHK, hK, hcount⟩
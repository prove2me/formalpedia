-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_completion__p2m_886ba71e_17fb_4cdf_ac77_08f2d3101909_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:52:35.394117+00:00
-- url     : https://prove2.me/submissions/673c2ad0-cc04-41ae-b4f5-270974f80812

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension__p2m_a751ad37_41e6_4dc6_8ec5_fa27c83e40b5_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_face_equations__p2m_a751ad37_41e6_4dc6_8ec5_fa27c83e40b5_a1
import Theorems.Thm_WilliamsonShmoys_planar_face_equations_imply_edge_count__p2m_a751ad37_41e6_4dc6_8ec5_fa27c83e40b5_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V) :
    ∃ G : SimpleGraph V,
      H ≤ G ∧
      WilliamsonShmoys.HasPlanarDrawingOn G ∧
      G.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨G, hHG, hG, hMax⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_extension__p2m_a751ad37_41e6_4dc6_8ec5_fa27c83e40b5_a1
      H hH
  obtain ⟨f, hEuler, hTri⟩ :=
    WilliamsonShmoys.maximal_planar_drawing_face_equations__p2m_a751ad37_41e6_4dc6_8ec5_fa27c83e40b5_a1
      G hG hMax hV
  have hCount :=
    WilliamsonShmoys.planar_face_equations_imply_edge_count__p2m_a751ad37_41e6_4dc6_8ec5_fa27c83e40b5_a1
      (Fintype.card V) G.edgeSet.ncard f hEuler hTri
  exact ⟨G, hHG, hG, hCount⟩
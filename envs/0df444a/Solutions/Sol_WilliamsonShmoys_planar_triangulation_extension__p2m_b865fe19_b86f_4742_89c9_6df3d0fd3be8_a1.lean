-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_extension__p2m_b865fe19_b86f_4742_89c9_6df3d0fd3be8_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:39:52.484428+00:00
-- url     : https://prove2.me/submissions/673b7bb4-1853-46ce-9810-acd5840ac533

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension__p2m_b5de7163_4173_4d75_853e_5e2f32ae30ae_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_b5de7163_4173_4d75_853e_5e2f32ae30ae_a1

set_option autoImplicit false

 theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hplanar : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      K.edgeSet ⊆ H.edgeSet ∧
      H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨H, hKH, hHplanar, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_extension__p2m_b5de7163_4173_4d75_853e_5e2f32ae30ae_a1
      K hplanar hcard
  have hcount :=
    WilliamsonShmoys.maximal_planar_edge_count__p2m_b5de7163_4173_4d75_853e_5e2f32ae30ae_a1
      H hHplanar hmax hcard
  exact ⟨H, hKH, hcount⟩
-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_has_triangulation
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T08:28:27.776046+00:00
-- url     : https://prove2.me/submissions/be2f9427-c6dd-4560-a426-9d647a638cc0

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_drawing_extension_00187ed1_118c_4569_ae21_cc59aa929691
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_00187ed1_118c_4569_ae21_cc59aa929691

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V,
      K.edgeSet ⊆ L.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      L.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨L, hKL, hL, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_drawing_extension_00187ed1_118c_4569_ae21_cc59aa929691 K hK
  exact ⟨L, hKL, hL,
    WilliamsonShmoys.maximal_planar_drawing_edge_count_00187ed1_118c_4569_ae21_cc59aa929691 L hL hV hmax⟩
-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_extension_to_triangulation
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T07:46:01.636891+00:00
-- url     : https://prove2.me/submissions/d7d3a3f1-89b1-4266-b13e-38a2c991a53e

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_extension_finite_maximal
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_from_embedding

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N) :
    ∃ P : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn P ∧
      N.edgeSet ⊆ P.edgeSet ∧
      P.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨P, hP, hNP, hMax⟩ :=
    WilliamsonShmoys.planar_drawing_extension_finite_maximal N hCard hN
  exact ⟨P, hP, hNP,
    WilliamsonShmoys.maximal_planar_drawing_edge_count_from_embedding P hCard hP hMax⟩
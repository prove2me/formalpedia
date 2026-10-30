-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_has_exact_edge_count_completion_for_maximality
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T22:55:09.07459+00:00
-- url     : https://prove2.me/submissions/7f77f6cc-85f0-49be-855b-351892108b89

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_edge_maximal_planar_completion_eb48bd77
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_has_exact_edge_count_eb48bd77

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hDraw : HasPlanarDrawingOn N)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V,
      N.edgeSet ⊆ L.edgeSet ∧
      HasPlanarDrawingOn L ∧
      L.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨L, hSub, hDrawL, hMax⟩ :=
    WilliamsonShmoys.exists_edge_maximal_planar_completion_eb48bd77 N hDraw hCard
  exact ⟨L, hSub, hDrawL,
    WilliamsonShmoys.maximal_planar_drawing_has_exact_edge_count_eb48bd77
      L hDrawL hCard hMax⟩
-- Prove2me | solution 1 for WilliamsonShmoys.planarDrawingOn_has_triangulated_supergraph
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T12:59:06.610208+00:00
-- url     : https://prove2.me/submissions/27b36243-c766-4847-8a10-bfe19817c313

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planarDrawingOn_has_maximal_supergraph
import Theorems.Thm_WilliamsonShmoys_maximalPlanarDrawingOn_has_triangulation_count_c1858b2a_2070_4db6_a0f4_ae5f3dacb3cc

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (R : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hR : WilliamsonShmoys.HasPlanarDrawingOn R) :
    ∃ S : SimpleGraph V, R ≤ S ∧
      WilliamsonShmoys.HasPlanarDrawingOn S ∧
      S.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨S, hRS, hS, hMax⟩ :=
    WilliamsonShmoys.planarDrawingOn_has_maximal_supergraph R hCard hR
  have hCount :=
    WilliamsonShmoys.maximalPlanarDrawingOn_has_triangulation_count_c1858b2a_2070_4db6_a0f4_ae5f3dacb3cc
      S hS hMax hCard
  exact ⟨S, hRS, hS, hCount⟩
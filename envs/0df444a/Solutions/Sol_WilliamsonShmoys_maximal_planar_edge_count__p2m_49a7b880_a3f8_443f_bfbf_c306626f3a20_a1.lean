-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_49a7b880_a3f8_443f_bfbf_c306626f3a20_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T06:51:24.235992+00:00
-- url     : https://prove2.me/submissions/e4499e43-6ecb-48fe-bf78-98451d5847f9

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_triangulated_edge_count__p2m_585fc207_795e_4bf8_b875_c8bd05631f21_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hMax : ∀ M : SimpleGraph V,
      L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M ≤ L)
    (hCard : 3 ≤ Fintype.card V) :
    L.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨M, hLM, hM, hCount⟩ :=
    WilliamsonShmoys.planar_supergraph_triangulated_edge_count__p2m_585fc207_795e_4bf8_b875_c8bd05631f21_a1 L hL hCard
  have hML : M ≤ L := hMax M hLM hM
  have hEq : M = L := le_antisymm hML hLM
  rw [hEq] at hCount
  exact hCount
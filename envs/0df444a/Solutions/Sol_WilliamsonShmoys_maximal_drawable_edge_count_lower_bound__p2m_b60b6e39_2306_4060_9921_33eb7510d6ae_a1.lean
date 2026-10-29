-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_edge_count_lower_bound__p2m_b60b6e39_2306_4060_9921_33eb7510d6ae_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T20:41:33.925771+00:00
-- url     : https://prove2.me/submissions/e5f0b406-8f7f-425c-8c9a-21308a0a1858

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_supergraph_exact_edge_count

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hMax : ∀ M : SimpleGraph V, L ≤ M →
      WilliamsonShmoys.HasPlanarDrawingOn M → L = M)
    (hCard : 3 ≤ Fintype.card V) :
    3 * Fintype.card V ≤ L.edgeSet.ncard + 6 := by
  obtain ⟨M, hLM, hMDraw, hMCard⟩ :=
    WilliamsonShmoys.planar_triangulation_supergraph_exact_edge_count
      L hCard hDraw
  have hEq : L = M := hMax M hLM hMDraw
  rw [hEq]
  omega

-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_7d768a9f_2454_410a_aba4_32911cd0fa44_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T09:19:57.484353+00:00
-- url     : https://prove2.me/submissions/a050cf7b-edad-4d0c-abf0-ad37fab3348f

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_supergraph_exact_edge_count__p2m_a2753149_6560_4e8a_9416_1a8ad9b1c226_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V,
      H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H)
    (hV : 3 ≤ Fintype.card V) :
    3 * Fintype.card V - 6 ≤ H.edgeSet.ncard := by
  obtain ⟨K, hHK, hKdraw, hKedges⟩ :=
    WilliamsonShmoys.planar_triangulation_supergraph_exact_edge_count__p2m_a2753149_6560_4e8a_9416_1a8ad9b1c226_a1
      H hV hH
  have hKH : K = H := hmax K hHK hKdraw
  simpa [hKH] using hKedges.le
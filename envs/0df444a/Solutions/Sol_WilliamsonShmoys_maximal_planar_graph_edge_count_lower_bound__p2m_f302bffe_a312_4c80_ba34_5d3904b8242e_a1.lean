-- Prove2me | solution 1 for WilliamsonShmoys_maximal_planar_graph_edge_count_lower_bound__p2m_f302bffe_a312_4c80_ba34_5d3904b8242e_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T15:28:24.825201+00:00
-- url     : https://prove2.me/submissions/651d64e4-2eba-44a3-8c0b-287f153f3cd6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_edge_lower_bound__p2m_fab97ac1_520c_4abf_97c8_3a81171a10a9_a1
import Mathlib
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hMax : ∀ M : SimpleGraph V,
      L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M = L) :
    3 * Fintype.card V - 6 ≤ L.edgeSet.ncard := by
  obtain ⟨M, hLM, hM, hbound⟩ :=
    WilliamsonShmoys.planar_supergraph_edge_lower_bound__p2m_fab97ac1_520c_4abf_97c8_3a81171a10a9_a1
      L hcard hL
  have hEq : M = L := hMax M hLM hM
  simpa [hEq] using hbound
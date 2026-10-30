-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_completion_exact_edge_count__p2m_eb21a977_2509_4ef4_8e83_e4c522788ebf_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T09:18:45.429126+00:00
-- url     : https://prove2.me/submissions/dee41d80-4500-4749-a80c-29bcf37cf6bb
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph__p2m_52c72b1a_727a_4125_917a_c27d4ca055ae_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph_edge_count__p2m_52c72b1a_727a_4125_917a_c27d4ca055ae_a1

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V,
      M ≤ N ∧
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      N.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨N, hMN, hNDraw, hMaximal⟩ :=
    WilliamsonShmoys.maximal_planar_supergraph__p2m_52c72b1a_727a_4125_917a_c27d4ca055ae_a1
      M hCard hDraw
  refine ⟨N, hMN, hNDraw, ?_⟩
  exact WilliamsonShmoys.maximal_planar_supergraph_edge_count__p2m_52c72b1a_727a_4125_917a_c27d4ca055ae_a1
    N hCard hNDraw hMaximal
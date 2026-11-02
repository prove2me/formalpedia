-- Prove2me | solution 1 for WilliamsonShmoys.planar_supergraph_edge_lower_bound__p2m_fab97ac1_520c_4abf_97c8_3a81171a10a9_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T15:45:37.794897+00:00
-- url     : https://prove2.me/submissions/f3e15295-5600-4053-8d8e-7fb1bd31d7d3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_exists_edge_maximal_planar_supergraph__p2m_73c11356_224a_46ad_adf9_93b5e9cc00b6_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound__p2m_73c11356_224a_46ad_adf9_93b5e9cc00b6_a1
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V, L ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧
      3 * Fintype.card V - 6 ≤ M.edgeSet.ncard := by
  obtain ⟨M, hLM, hM, hmax⟩ :=
    WilliamsonShmoys.exists_edge_maximal_planar_supergraph__p2m_73c11356_224a_46ad_adf9_93b5e9cc00b6_a1
      L hL
  exact ⟨M, hLM, hM,
    WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_73c11356_224a_46ad_adf9_93b5e9cc00b6_a1
      M hM hmax hcard⟩
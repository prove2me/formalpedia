-- Prove2me | solution 1 for WilliamsonShmoys.planar_supergraph_with_triangulation_edge_count__p2m_700bbd5b_00a3_4afe_b6e3_ec004e650a47_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T03:21:12.677208+00:00
-- url     : https://prove2.me/submissions/10f85e52-e3cb-4ebd-bca2-9990231b4cfe
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph__p2m_5adcef95_78da_42fb_a9d7_cfb89d379e66_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_5adcef95_78da_42fb_a9d7_cfb89d379e66_a1

set_option autoImplicit false

open scoped BigOperators

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ L : SimpleGraph V, G ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
      L.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨L, hGL, hL, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_5adcef95_78da_42fb_a9d7_cfb89d379e66_a1
      G hcard hG
  refine ⟨L, hGL, hL, ?_⟩
  exact WilliamsonShmoys.maximal_planar_edge_count__p2m_5adcef95_78da_42fb_a9d7_cfb89d379e66_a1
    L hcard hL hmax
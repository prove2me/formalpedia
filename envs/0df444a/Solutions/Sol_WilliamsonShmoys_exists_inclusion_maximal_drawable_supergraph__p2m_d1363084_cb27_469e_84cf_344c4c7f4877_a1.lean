-- Prove2me | solution 1 for WilliamsonShmoys.exists_inclusion_maximal_drawable_supergraph__p2m_d1363084_cb27_469e_84cf_344c4c7f4877_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:35:47.125125+00:00
-- url     : https://prove2.me/submissions/cedb05da-5fa1-4866-a88f-c634a39ed269

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_FiniteSimpleGraph_exists_maximal_supergraph__p2m_ebc26ecc_dfea_4863_8cab_260c69e4997d_a2

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ K : SimpleGraph V,
      G ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      (∀ H : SimpleGraph V,
        G ≤ H → WilliamsonShmoys.HasPlanarDrawingOn H → K ≤ H → H ≤ K) := by
  exact FiniteSimpleGraph.exists_maximal_supergraph__p2m_ebc26ecc_dfea_4863_8cab_260c69e4997d_a2
    G WilliamsonShmoys.HasPlanarDrawingOn hG
-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_bound_for_maximal_planar_exact_edge_count__p2m_861504bb_9b69_4346_abcf_17510b6445ad_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T01:58:01.892593+00:00
-- url     : https://prove2.me/submissions/91e07b86-b725-47d8-a651-ffcdc968015c

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_triangulation_edge_count__p2m_4c7ec41a_7a94_4be9_ac1a_23f63e19fba0_a1
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    (letI : DecidableRel G.Adj := Classical.decRel G.Adj
     G.edgeFinset.card ≤ 3 * Fintype.card V - 6) := by
  classical
  letI : DecidableRel G.Adj := Classical.decRel G.Adj
  obtain ⟨H, hGH, hH, hcardH⟩ :=
    WilliamsonShmoys.planar_supergraph_triangulation_edge_count__p2m_4c7ec41a_7a94_4be9_ac1a_23f63e19fba0_a1
      G hcard hG
  letI : DecidableRel H.Adj := Classical.decRel H.Adj
  change G.edgeFinset.card ≤ 3 * Fintype.card V - 6
  calc
    G.edgeFinset.card ≤ H.edgeFinset.card :=
      Finset.card_le_card (SimpleGraph.edgeFinset_mono hGH)
    _ = 3 * Fintype.card V - 6 := hcardH
-- Prove2me | solution 1 for WilliamsonShmoys.planar_simple_graph_edge_bound__p2m_9b84e475_7be1_4007_a2e0_d2e99948fc5d_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T22:27:12.158582+00:00
-- url     : https://prove2.me/submissions/2277ff0a-aafb-48b5-a6c1-6a9a2b0578a7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_planar_supergraph_with_extremal_edge_count__p2m_c24261b1_eccd_4339_a0db_50a7175ab071_a2
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G)
    (dG : DecidableRel G.Adj)
    (hcard : 3 ≤ Fintype.card V) :
    (letI : DecidableRel G.Adj := dG;
      G.edgeFinset.card ≤ 3 * Fintype.card V - 6) := by
  classical
  letI : DecidableRel G.Adj := dG
  obtain ⟨H, hGH, _hH, hHcard⟩ :=
    WilliamsonShmoys.exists_planar_supergraph_with_extremal_edge_count__p2m_c24261b1_eccd_4339_a0db_50a7175ab071_a2
      G hG hcard
  calc
    G.edgeFinset.card ≤ H.edgeFinset.card := Finset.card_le_card (SimpleGraph.edgeFinset_mono hGH)
    _ = 3 * Fintype.card V - 6 := hHcard
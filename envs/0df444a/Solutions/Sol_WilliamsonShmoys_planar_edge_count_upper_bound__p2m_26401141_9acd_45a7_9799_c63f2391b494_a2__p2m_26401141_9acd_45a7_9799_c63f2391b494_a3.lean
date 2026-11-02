-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_upper_bound__p2m_26401141_9acd_45a7_9799_c63f2391b494_a2__p2m_26401141_9acd_45a7_9799_c63f2391b494_a3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T06:41:24.802653+00:00
-- url     : https://prove2.me/submissions/3617fcd2-9477-457a-9684-79f4f014eaa3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension__p2m_16d3ee06_3460_49bf_bee5_c29e2e73cd73_a2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count__p2m_16d3ee06_3460_49bf_bee5_c29e2e73cd73_a2
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : HasPlanarDrawingOn G)
    (hcard : 3 ≤ Fintype.card V) :
    letI : ∀ H : SimpleGraph V, DecidableRel H.Adj :=
      fun H => Classical.decRel H.Adj
    G.edgeFinset.card ≤ 3 * Fintype.card V - 6 := by
  classical
  letI : ∀ H : SimpleGraph V, DecidableRel H.Adj :=
    fun H => Classical.decRel H.Adj
  obtain ⟨H, hGH, hHplanar, hHmax, hcardGH⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_extension__p2m_16d3ee06_3460_49bf_bee5_c29e2e73cd73_a2 G hG
  have hHeq :=
    WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_16d3ee06_3460_49bf_bee5_c29e2e73cd73_a2 H hHplanar hHmax hcard
  calc
    G.edgeFinset.card ≤ H.edgeFinset.card := hcardGH
    _ = 3 * Fintype.card V - 6 := hHeq
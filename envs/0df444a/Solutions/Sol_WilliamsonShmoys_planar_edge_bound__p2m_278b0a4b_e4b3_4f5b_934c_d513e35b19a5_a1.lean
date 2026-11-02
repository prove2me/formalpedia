-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_bound__p2m_278b0a4b_e4b3_4f5b_934c_d513e35b19a5_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T13:04:07.236119+00:00
-- url     : https://prove2.me/submissions/3fb74326-95f4-4487-b9f0-8e70fbb3e05b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_extension__p2m_1508a319_0bdf_43a6_9c8f_5ec7d4360d47_a2
import Theorems.Thm_WilliamsonShmoys_small_graph_edge_bound__p2m_1508a319_0bdf_43a6_9c8f_5ec7d4360d47_a2
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G) :
    letI : DecidableRel G.Adj := Classical.decRel _
    G.edgeFinset.card ≤ 3 * Fintype.card V - 3 := by
  classical
  letI : DecidableRel G.Adj := Classical.decRel _
  by_cases hsmall : Fintype.card V < 3
  · exact WilliamsonShmoys.small_graph_edge_bound__p2m_1508a319_0bdf_43a6_9c8f_5ec7d4360d47_a2 G hsmall
  · obtain ⟨H, hGH, _hHplanar, hHcard⟩ :=
      WilliamsonShmoys.planar_drawing_triangulation_extension__p2m_1508a319_0bdf_43a6_9c8f_5ec7d4360d47_a2
        G hG (by omega)
    have hedges : G.edgeFinset.card ≤ H.edgeFinset.card :=
      Finset.card_le_card (SimpleGraph.edgeFinset_mono hGH)
    rw [hHcard] at hedges
    omega